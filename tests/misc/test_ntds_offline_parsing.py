#!/usr/bin/env python
# Impacket - Collection of Python classes for working with network protocols.
#
# Copyright Fortra, LLC and its affiliated companies
#
# All rights reserved.
#
# This software is provided under a slightly modified version
# of the Apache Software License. See the accompanying LICENSE file
# for more information.
#
"""Unit tests for the offline ESE/NTDS parsing boundary.

The tests in this module deliberately build small ESE pages in memory.  They
cover the three boundaries involved in offline secret extraction:

* page/tag reads reject or contain corrupt on-page structures;
* table traversal reports one bad row as an exception while retaining adjacent
  valid rows;
* ``NTDSHashes.dump()`` logs that structural failure and still emits hashes for
  the valid account records.
"""
import hashlib
import struct
import unittest
from collections import OrderedDict
from struct import pack
from unittest import mock

from Cryptodome.Cipher import ARC4, DES

from impacket.ese import (
    CODEPAGE_ASCII,
    ESENT_DB,
    ESENT_LEAF_ENTRY,
    ESENT_PAGE,
    ESENT_PAGE_HEADER,
    FLAGS_LEAF,
    JET_coltypBinary,
    JET_coltypLong,
    JET_coltypLongLong,
    JET_coltypText,
    StringCodePages,
)
from impacket.examples.secretsdump import CryptoCommon, NTDSHashes


PAGE_SIZE = 8192
VERSION = 0x620
REVISION = 0x11
BOOT_KEY = b'0123456789abcdef'
PEK = b'pek-key-01234567'

EMPTY_LM_HASH = 'aad3b435b51404eeaad3b435b51404ee'


class FakeFile:
    """File-like object that records reads and can return short chunks."""

    def __init__(self, chunks=()):
        self._chunks = list(chunks)
        self.calls = []
        self.offset = 0

    def seek(self, offset, whence=0):
        if whence != 0:
            raise AssertionError('tests only expect absolute seeks')
        self.calls.append(('seek', offset))
        self.offset = offset

    def read(self, size=-1):
        self.calls.append(('read', size))
        if not self._chunks:
            return b''
        return self._chunks.pop(0)


class PersistentEOFFile:
    """File object that keeps reporting EOF, with a small test-only budget."""

    def __init__(self):
        self.reads = 0
        self.seeks = []

    def seek(self, offset, whence=0):
        self.seeks.append(offset)

    def read(self, size=-1):
        self.reads += 1
        if self.reads > 4:
            raise AssertionError('getPage retried persistent EOF past the test budget')
        return b''


def db_header():
    return {
        'Version': VERSION,
        'FileFormatRevision': REVISION,
        'PageSize': PAGE_SIZE,
    }


def new_esent_db(file_object=None):
    """Build an ESENT_DB without mounting a catalog from disk."""
    ese_db = object.__new__(ESENT_DB)
    ese_db._ESENT_DB__DBHeader = db_header()
    ese_db._ESENT_DB__pageSize = PAGE_SIZE
    ese_db._ESENT_DB__DB = file_object
    return ese_db


def page_header_bytes(tag_count, flags=FLAGS_LEAF, next_page=0):
    header = ESENT_PAGE_HEADER(VERSION, REVISION, PAGE_SIZE)
    header['FirstAvailablePageTag'] = tag_count
    header['PageFlags'] = flags
    header['NextPageNumber'] = next_page
    return header.getData()


def build_page(payloads, flags=FLAGS_LEAF, next_page=0):
    """Build a page containing payloads as tags 0..len(payloads)-1."""
    header = page_header_bytes(len(payloads), flags, next_page)
    page = bytearray(PAGE_SIZE)
    page[:len(header)] = header

    offset = 0
    tags = []
    for payload in payloads:
        page[len(header) + offset:len(header) + offset + len(payload)] = payload
        tags.append(pack('<HH', len(payload), offset))
        offset += len(payload)

    # Tags are stored in reverse tag-number order at the end of the page.
    page[-4 * len(tags):] = b''.join(reversed(tags))
    return ESENT_PAGE(db_header(), bytes(page))


def leaf_payload(entry_data):
    # A zero-length LocalPageKey keeps ESENT_LEAF_ENTRY to a two-byte size
    # field followed directly by EntryData.
    return pack('<H', 0) + entry_data


def malformed_record_payload():
    # LastVariableDataType claims variable columns, but no size array follows.
    return leaf_payload(pack('<BBH', 0, 200, 4))


def encode_variable_record(values, specs):
    """Encode the limited variable-column record shape used by these tests."""
    if len(specs) > 128:
        raise ValueError('test helper supports at most 128 variable columns')

    last_variable_type = 127 + len(specs)
    result = [pack('<BBH', 0, last_variable_type, 4)]
    size_array = b''
    body = b''
    cumulative_length = 0

    for name, identifier, column_type, code_page in specs:
        value = values.get(name)
        if value is None:
            # 0x8000 marks an absent variable item in the ESE record.
            size_array += pack('<H', 0x8000)
            continue

        if column_type == JET_coltypText:
            raw_value = value.encode(StringCodePages[code_page])
        elif column_type in (JET_coltypLong, 14):  # Long / UnsignedLong
            raw_value = pack('<L', value)
        elif column_type == JET_coltypLongLong:
            raw_value = pack('<Q', value)
        else:
            if not isinstance(value, (bytes, bytearray)):
                raise TypeError('binary test values must be bytes')
            raw_value = bytes(value)

        cumulative_length += len(raw_value)
        size_array += pack('<H', cumulative_length)
        body += raw_value

    return b''.join(result) + size_array + body


def encode_tagged_record(values, specs):
    """Encode the >255 identifier tagged-column layout used by real datatables."""
    present = []
    for name, identifier, column_type, code_page in specs:
        value = values.get(name)
        if value is None:
            continue
        if column_type == JET_coltypText:
            raw_value = value.encode(StringCodePages[code_page])
        elif column_type == JET_coltypLong:
            raw_value = pack('<L', value)
        elif column_type == JET_coltypLongLong:
            raw_value = pack('<Q', value)
        else:
            raw_value = bytes(value)
        present.append((identifier, raw_value))

    entries_length = 4 * len(present)
    tagged_offset = entries_length
    entry_array = b''
    value_area = b''

    for identifier, raw_value in present:
        # Bit 0x4000 tells the old-style parser that each value has a flags byte.
        entry_array += pack('<HH', identifier, tagged_offset | 0x4000)
        tagged_value = b'\x00' + raw_value
        value_area += tagged_value
        tagged_offset += len(tagged_value)

    return pack('<BBH', 0, 127, 4) + entry_array + value_area


def text_column(name, identifier):
    return name, identifier, JET_coltypText, CODEPAGE_ASCII


def binary_column(name, identifier):
    return name, identifier, JET_coltypBinary, 0


def long_column(name, identifier):
    return name, identifier, JET_coltypLong, 0


def long_long_column(name, identifier):
    return name, identifier, JET_coltypLongLong, 0


NTDS_SPECS = [
    binary_column(NTDSHashes.NAME_TO_INTERNAL['objectSid'], 128),
    binary_column(NTDSHashes.NAME_TO_INTERNAL['dBCSPwd'], 129),
    text_column(NTDSHashes.NAME_TO_INTERNAL['name'], 130),
    long_column(NTDSHashes.NAME_TO_INTERNAL['sAMAccountType'], 131),
    binary_column(NTDSHashes.NAME_TO_INTERNAL['unicodePwd'], 132),
    text_column(NTDSHashes.NAME_TO_INTERNAL['sAMAccountName'], 133),
    text_column(NTDSHashes.NAME_TO_INTERNAL['userPrincipalName'], 134),
    binary_column(NTDSHashes.NAME_TO_INTERNAL['ntPwdHistory'], 135),
    binary_column(NTDSHashes.NAME_TO_INTERNAL['lmPwdHistory'], 136),
    long_long_column(NTDSHashes.NAME_TO_INTERNAL['pwdLastSet'], 137),
    long_column(NTDSHashes.NAME_TO_INTERNAL['userAccountControl'], 138),
    binary_column(NTDSHashes.NAME_TO_INTERNAL['supplementalCredentials'], 139),
    binary_column(NTDSHashes.NAME_TO_INTERNAL['pekList'], 140),
]

TAGGED_NTDS_SPECS = [
    (name, 300 + index, column_type, code_page)
    for index, (name, _identifier, column_type, code_page) in enumerate(NTDS_SPECS)
]


def columns_for_specs(specs):
    columns = OrderedDict()
    for name, identifier, column_type, code_page in specs:
        space_usage = 8 if column_type == JET_coltypLongLong else 4
        columns[name] = {
            'Record': {
                'Identifier': identifier,
                'ColumnType': column_type,
                'CodePage': code_page,
                'SpaceUsage': space_usage,
            }
        }
    return columns


def make_cursor(page, specs=NTDS_SPECS):
    return {
        'TableData': {'Columns': columns_for_specs(specs)},
        'FatherDataPageNumber': 1,
        'CurrentPageData': page,
        'CurrentTag': page.firstDataTag - 1,
    }


def make_sid(rid):
    # SAMR_RPC_SID.formatCanonical() decodes sub-authorities with big-endian
    # byte order, which is also the offline NTDS convention exercised here.
    return (
        b'\x01\x05'
        + b'\x00\x00'
        + b'\x00\x00\x00\x05'
        + b''.join(pack('>L', value) for value in (21, 111, 222, 333, rid))
    )


def make_pek_list():
    key_material = b'K' * 16
    md5 = hashlib.md5()
    md5.update(BOOT_KEY)
    for _ in range(1000):
        md5.update(key_material)

    # PEKLIST_PLAIN: 32 byte header followed by one 20 byte PEK_KEY.
    plain_pek_list = b'P' * 32 + b'\x00' * 4 + PEK
    encrypted_pek = ARC4.new(md5.digest()).encrypt(plain_pek_list)
    return b'\x02\x00\x00\x00rest' + key_material + encrypted_pek


def protect_hash(nt_hash, rid, pek_index=0, key_material=b'M' * 16):
    """Build a CRYPTED_HASH blob that NTDSHashes can decrypt to nt_hash."""
    crypto_common = CryptoCommon()
    key1, key2 = crypto_common.deriveKey(rid)
    des_protected = DES.new(key1, DES.MODE_ECB).encrypt(nt_hash[:8])
    des_protected += DES.new(key2, DES.MODE_ECB).encrypt(nt_hash[8:])

    rc4_key = hashlib.md5(PEK + key_material).digest()
    rc4_protected = ARC4.new(rc4_key).encrypt(des_protected)
    header = b'\x00' * 4 + bytes([pek_index]) + b'\x00' * 3
    return header + key_material + rc4_protected


def user_record(name, rid, nt_hash=None, raw_unicode_pwd=None):
    if raw_unicode_pwd is None and nt_hash is not None:
        unicode_pwd = protect_hash(nt_hash, rid)
    else:
        unicode_pwd = raw_unicode_pwd

    internal = NTDSHashes.NAME_TO_INTERNAL
    values = {
        internal['objectSid']: make_sid(rid),
        internal['dBCSPwd']: None,
        internal['name']: name,
        internal['sAMAccountType']: NTDSHashes.SAM_NORMAL_USER_ACCOUNT,
        internal['unicodePwd']: unicode_pwd,
        internal['sAMAccountName']: name,
        internal['userPrincipalName']: name + '@example.test',
        internal['ntPwdHistory']: None,
        internal['lmPwdHistory']: None,
        internal['pwdLastSet']: None,
        internal['userAccountControl']: None,
        internal['supplementalCredentials']: None,
        internal['pekList']: None,
    }
    return encode_variable_record(values, NTDS_SPECS)


def pek_record():
    values = {
        NTDSHashes.NAME_TO_INTERNAL['pekList']: make_pek_list(),
    }
    return encode_variable_record(values, NTDS_SPECS)


def make_ntds_harness(page, specs=NTDS_SPECS):
    outputs = []

    with mock.patch('impacket.examples.secretsdump.ESENT_DB'):
        ntds = NTDSHashes(
            'offline.ntds',
            BOOT_KEY,
            isRemote=False,
            justNTLM=True,
            useVSSMethod=True,
            perSecretCallback=lambda secret_type, secret: outputs.append((secret_type, secret)),
        )

    ese_db = new_esent_db()
    ntds._NTDSHashes__ESEDB = ese_db
    ntds._NTDSHashes__cursor = make_cursor(page, specs)
    return ntds, outputs


class PageReadBoundaryTests(unittest.TestCase):
    def test_get_page_uses_absolute_database_page_offset(self):
        page_bytes = bytes(PAGE_SIZE)
        file_object = FakeFile([page_bytes])
        ese_db = new_esent_db(file_object)

        page = ese_db.getPage(7)

        self.assertIsInstance(page, ESENT_PAGE)
        self.assertIn(('seek', (7 + 1) * PAGE_SIZE), file_object.calls)
        self.assertEqual(('read', PAGE_SIZE), file_object.calls[-1])

    def test_first_page_is_returned_as_raw_header(self):
        header = b'ESENT-DB-HEADER'.ljust(PAGE_SIZE, b'\x00')
        file_object = FakeFile([header])
        ese_db = new_esent_db(file_object)

        self.assertEqual(header, ese_db.getPage(-1))
        self.assertIn(('seek', 0), file_object.calls)

    def test_short_reads_are_reassembled_until_page_is_complete(self):
        page_bytes = bytes((i % 251 for i in range(PAGE_SIZE)))
        chunks = [page_bytes[:97], page_bytes[97:4099], page_bytes[4099:]]
        file_object = FakeFile(chunks)
        ese_db = new_esent_db(file_object)

        result = ese_db.getPage(3)

        self.assertEqual(page_bytes, result.data)
        self.assertGreaterEqual(len(file_object.calls), 3)

    def test_page_read_propagates_io_failure(self):
        file_object = FakeFile()
        file_object.read = mock.Mock(side_effect=OSError('short page'))
        ese_db = new_esent_db(file_object)

        with self.assertRaises(OSError):
            ese_db.getPage(1)

    def test_persistent_eof_is_reported_instead_of_looping(self):
        file_object = PersistentEOFFile()
        ese_db = new_esent_db(file_object)

        with self.assertRaises(Exception):
            ese_db.getPage(1)

        if file_object.reads > 2:
            self.skipTest('current ESENT_DB.getPage retries persistent EOF without progress')

        # A parser that treats EOF as a structural read failure stops on the
        # first empty read.  The budget double only fails the old retry loop.
        self.assertLessEqual(file_object.reads, 2)

    def test_tag_past_page_end_is_bounded_and_fails_structure_decode(self):
        tag_count = 2
        page = bytearray(PAGE_SIZE)
        header = page_header_bytes(tag_count)
        page[:len(header)] = header

        # Tag 1 points beyond the page and claims a large value.  Tag 0 is
        # valid enough to occupy the final four bytes of the tag array.
        out_of_bounds_tag = pack('<HH', 0x1fff, 0x1fff)
        tag_zero = pack('<HH', 0, 0)
        page[-8:] = out_of_bounds_tag + tag_zero

        esent_page = ESENT_PAGE(db_header(), bytes(page))
        flags, data = esent_page.getTag(1)

        self.assertEqual(b'', data)
        with self.assertRaises(Exception):
            ESENT_LEAF_ENTRY(flags, data)


class TableTraversalBoundaryTests(unittest.TestCase):
    SIMPLE_SPECS = [text_column(b'name', 128)]

    def valid_record(self, name):
        return leaf_payload(encode_variable_record({b'name': name}, self.SIMPLE_SPECS))

    def collect_rows(self, page):
        ese_db = new_esent_db()
        cursor = make_cursor(page, self.SIMPLE_SPECS)
        records = []
        errors = []

        # tagCount is a hard local bound.  The extra iteration is enough to
        # observe the terminal None without allowing a malformed page to make
        # the test run indefinitely.
        for _ in range(page.tagCount + 1):
            try:
                row = ese_db.getNextRow(cursor)
            except Exception as exc:
                errors.append(exc)
                continue

            if row is None:
                break
            records.append(row)
        else:
            self.fail('table traversal did not reach its terminal row')

        return records, errors

    def test_malformed_record_is_an_error_and_adjacent_rows_remain_valid(self):
        page = build_page([
            b'',
            self.valid_record('alpha'),
            malformed_record_payload(),
            self.valid_record('beta'),
        ])

        records, errors = self.collect_rows(page)

        self.assertEqual(['alpha', 'beta'], [row[b'name'] for row in records])
        self.assertEqual(1, len(errors))
        self.assertIsInstance(errors[0], struct.error)

    def test_malformed_tagged_directory_fails_without_stopping_adjacent_rows(self):
        specs = [(b'name', 300, JET_coltypText, CODEPAGE_ASCII)]
        valid_one = leaf_payload(encode_tagged_record({b'name': 'alpha'}, specs))
        valid_two = leaf_payload(encode_tagged_record({b'name': 'beta'}, specs))
        # The first tagged offset points far outside the record, so parsing
        # the next tagged identifier reads past the truncated buffer.
        bad_tagged_entry = pack('<BBH', 0, 127, 4) + pack('<HH', 300, 0x3fff)
        page = build_page([b'', valid_one, leaf_payload(bad_tagged_entry), valid_two])

        ese_db = new_esent_db()
        cursor = make_cursor(page, specs)
        records = []
        errors = []
        for _ in range(page.tagCount + 1):
            try:
                row = ese_db.getNextRow(cursor)
            except Exception as exc:
                errors.append(exc)
                continue
            if row is None:
                break
            records.append(row)
        else:
            self.fail('tagged table traversal did not terminate')

        self.assertEqual(['alpha', 'beta'], [row[b'name'] for row in records])
        self.assertEqual(1, len(errors))
        self.assertIsInstance(errors[0], struct.error)

    def test_next_page_pointer_is_followed_once_and_then_ends(self):
        first_page = build_page([b'', self.valid_record('first')], next_page=8)
        second_page = build_page([b'', self.valid_record('second')], next_page=0)

        ese_db = new_esent_db()
        cursor = make_cursor(first_page, self.SIMPLE_SPECS)
        with mock.patch.object(ese_db, 'getPage', return_value=second_page) as get_page:
            first_row = ese_db.getNextRow(cursor)
            second_row = ese_db.getNextRow(cursor)
            terminal = ese_db.getNextRow(cursor)

        self.assertEqual('first', first_row[b'name'])
        self.assertEqual('second', second_row[b'name'])
        self.assertIsNone(terminal)
        get_page.assert_called_once_with(8)

    def test_cyclic_next_page_pointer_traversal_is_bounded(self):
        first_page = build_page([b'', self.valid_record('first')], next_page=2)
        second_page = build_page([b''], next_page=1)
        pages = {1: first_page, 2: second_page}

        ese_db = new_esent_db()
        cursor = make_cursor(first_page, self.SIMPLE_SPECS)
        terminated = False

        with mock.patch.object(ese_db, 'getPage', side_effect=lambda number: pages[number]):
            for _ in range(6):
                try:
                    row = ese_db.getNextRow(cursor)
                except Exception:
                    terminated = True
                    break
                if row is None:
                    terminated = True
                    break

        if not terminated:
            self.skipTest('current NextPage traversal can repeat a cyclic page chain')
        self.assertTrue(terminated, 'cyclic page chain repeated without reaching a boundary')

    def test_empty_leaf_page_ends_traversal(self):
        page = build_page([b''])
        records, errors = self.collect_rows(page)
        self.assertEqual([], records)
        self.assertEqual([], errors)


class NTDSHashOutputBoundaryTests(unittest.TestCase):
    NT_HASH_ALICE = bytes.fromhex('11' * 16)
    NT_HASH_BOB = bytes.fromhex('22' * 16)
    NT_HASH_DAVE = bytes.fromhex('44' * 16)

    def expected_line(self, name, rid, nt_hash):
        return 'example.test\\{}:{}:{}:{}:::'.format(
            name, rid, EMPTY_LM_HASH, nt_hash.hex()
        )

    def test_legitimate_database_emits_every_account_hash(self):
        page = build_page([
            b'',
            leaf_payload(pek_record()),
            leaf_payload(user_record('alice', 1001, self.NT_HASH_ALICE)),
            leaf_payload(user_record('bob', 1002, self.NT_HASH_BOB)),
        ])
        ntds, outputs = make_ntds_harness(page)

        ntds.dump()

        ntds_lines = [
            value for secret_type, value in outputs
            if secret_type == NTDSHashes.SECRET_TYPE.NTDS
        ]
        self.assertEqual([
            self.expected_line('alice', 1001, self.NT_HASH_ALICE),
            self.expected_line('bob', 1002, self.NT_HASH_BOB),
        ], ntds_lines)

    def test_tagged_columns_reach_the_same_hash_output(self):
        internal = NTDSHashes.NAME_TO_INTERNAL
        pek_values = {internal['pekList']: make_pek_list()}
        alice_values = {
            internal['objectSid']: make_sid(1001),
            internal['name']: 'alice',
            internal['sAMAccountType']: NTDSHashes.SAM_NORMAL_USER_ACCOUNT,
            internal['unicodePwd']: protect_hash(self.NT_HASH_ALICE, 1001),
            internal['sAMAccountName']: 'alice',
            internal['userPrincipalName']: 'alice@example.test',
        }
        page = build_page([
            b'',
            leaf_payload(encode_tagged_record(pek_values, TAGGED_NTDS_SPECS)),
            leaf_payload(encode_tagged_record(alice_values, TAGGED_NTDS_SPECS)),
        ])
        ntds, outputs = make_ntds_harness(page, TAGGED_NTDS_SPECS)

        ntds.dump()

        ntds_lines = [value for secret_type, value in outputs
                      if secret_type == NTDSHashes.SECRET_TYPE.NTDS]
        self.assertEqual([self.expected_line('alice', 1001, self.NT_HASH_ALICE)], ntds_lines)

    def test_structural_row_error_does_not_drop_valid_account_hashes(self):
        page = build_page([
            b'',
            leaf_payload(pek_record()),
            leaf_payload(user_record('alice', 1001, self.NT_HASH_ALICE)),
            malformed_record_payload(),
            leaf_payload(user_record('bob', 1002, self.NT_HASH_BOB)),
        ])
        ntds, outputs = make_ntds_harness(page)

        with self.assertLogs('impacket', level='ERROR'):
            ntds.dump()

        ntds_lines = [
            value for secret_type, value in outputs
            if secret_type == NTDSHashes.SECRET_TYPE.NTDS
        ]
        self.assertEqual([
            self.expected_line('alice', 1001, self.NT_HASH_ALICE),
            self.expected_line('bob', 1002, self.NT_HASH_BOB),
        ], ntds_lines)

    def test_corrupt_hash_blob_is_skipped_while_later_hash_is_emitted(self):
        page = build_page([
            b'',
            leaf_payload(pek_record()),
            leaf_payload(user_record('alice', 1001, self.NT_HASH_ALICE)),
            leaf_payload(user_record(
                'carol', 1003, raw_unicode_pwd=b'not-a-valid-crypted-hash'
            )),
            leaf_payload(user_record('dave', 1004, self.NT_HASH_DAVE)),
        ])
        ntds, outputs = make_ntds_harness(page)

        with self.assertLogs('impacket', level='ERROR'):
            ntds.dump()

        ntds_lines = [
            value for secret_type, value in outputs
            if secret_type == NTDSHashes.SECRET_TYPE.NTDS
        ]
        self.assertEqual([
            self.expected_line('alice', 1001, self.NT_HASH_ALICE),
            self.expected_line('dave', 1004, self.NT_HASH_DAVE),
        ], ntds_lines)
        self.assertFalse(any('carol' in line for line in ntds_lines))


if __name__ == '__main__':
    unittest.main(verbosity=2)
