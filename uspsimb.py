#!/usr/bin/env python
"""
uspsimb.py

United States Postal Service Intelligent Mail Barcode utility

Run from command line, can encode and decode routing/tracking information
into / from string composed of 'A', 'D', 'T', 'F' representing Ascender,
Descender, Tracking, and Full Bars of Intelligent Mail Barcode
A  D  T  F
|        |
|  |  |  |
   |     |

As a plugin for Gimp, utility will create a new text layer with barcode
Gimp plugin functionality requires USPSIMBStandard.ttf and USPSIMBCompact.ttf
Available at usps.gov

@author: erik lyon

"""
import sys
from collections import namedtuple
import array
import argparse

#pylint: disable-msg=W0614, W0401
GIMP_BLURB = \
'Converts routing and tracking info into USPS Intelligent Mail Barcode\
 and creates a text layer with the barcode'
GIMP_HELP = 'Input routing+tracking without spaces or other punctuation.\
Choose font: Compact 14pt, Standard 16pt'
GIMP_AUTHOR = 'erik lyon'
GIMP_COPYRIGHT = 'erik lyon'
GIMP_DATE = '11/28/12'

BAR_CONSTRUCTION_TABLE = [
'1 H 2 E 3', '2 B 10 A 0', '3 J 12 C 8', '4 F 5 G 11', '5 I 9 D 1',
'6 A 1 F 12', '7 C 5 B 8', '8 E 4 J 11', '9 G 3 I 10', '10 D 9 H 6',
'11 F 11 B 4', '12 I 5 C 12', '13 J 10 A 2', '14 H 1 G 7', '15 D 6 E 9',
'16 A 3 I 6', '17 G 4 C 7', '18 B 1 J 9', '19 H 10 F 2', '20 E 0 D 8',
'21 G 2 A 4', '22 I 11 B 0', '23 J 8 D 12', '24 C 6 H 7', '25 F 1 E 10',
'26 B 12 G 9', '27 H 3 I 0', '28 F 8 J 7', '29 E 6 C 10', '30 D 4 A 5',
'31 I 4 F 7', '32 H 11 B 9', '33 G 0 J 6', '34 A 6 E 8', '35 C 1 D 2',
'36 F 9 I 12', '37 E 11 G 1', '38 J 5 H 4', '39 D 3 B 2', '40 A 7 C 0',
'41 B 3 E 1', '42 G 10 D 5', '43 I 7 J 4', '44 C 11 F 6', '45 A 8 H 12',
'46 E 2 I 1', '47 F 10 D 0', '48 J 3 A 9', '49 G 5 C 4', '50 H 8 B 7',
'51 F 0 E 5', '52 C 3 A 10', '53 G 12 J 2', '54 D 11 B 6', '55 I 8 H 9',
'56 F 4 A 11', '57 B 5 C 2', '58 J 1 E 12', '59 I 3 G 6', '60 H 0 D 7',
'61 E 7 H 5', '62 A 12 B 11', '63 C 9 J 0', '64 G 8 F 3', '65 D 10 I 2'
]


def _bar_construction_table():
    """
    Construct list of namedtuples that map the inclusion of extenders on a bar
    to a particular bit in one of the 10 13-bit 'characters' referred to A-J
    """
    bar_table = []
    BarMap = namedtuple("BarMap", "desc_char desc_bit asc_char asc_bit")
    for element in BAR_CONSTRUCTION_TABLE:
        _, desc_char, desc_bit, asc_char, asc_bit = element.split(' ')
        bar_table.append(BarMap(desc_char, desc_bit, asc_char, asc_bit))

    return bar_table


def _reverse_unsigned_short(ushort):
    '''
    Reverse bits present in ushort
    :param ushort:
    '''
    rev = 0
    for _ in range(16):
        rev <<= 1
        rev |= ushort & 1
        ushort >>= 1
    return rev


def _lookup_table(table_type, length):
    """Return lookup table as array of length length"""
    assert table_type == 2 or table_type == 5, \
    'lookup_table type must be 2 or 5'
    assert length == 78 or length == 1287, \
    'lookup_table length must be 78 or 1279'
    lut = array.array('H')  # unsigned short
    for _ in range(length):
        lut.append(0)
    lut_lower = 0
    lut_upper = length - 1

    for count in range(8192):
        bit_count = bin(count).count('1')
        if bit_count != table_type:
            continue
        rev = _reverse_unsigned_short(count) >> 3
        if rev < count:
            continue
        if count == rev:
            lut[lut_upper] = count
            lut_upper -= 1
        else:
            lut[lut_lower] = count
            lut_lower += 1
            lut[lut_lower] = rev
            lut_lower += 1

    return lut


class IntelligentMailBarcode(object):
    '''
    Intelligent Mail Barcode class
    '''

    def __init__(self, barcode_id, st_id, mailer_id, serial_num, deliv_zip):
        '''
        Constructor
        '''
        assert isinstance(barcode_id, str) and barcode_id.isdigit()
        assert isinstance(st_id, str) and st_id.isdigit()
        assert isinstance(mailer_id, str) and mailer_id.isdigit()
        assert isinstance(serial_num, str) and serial_num.isdigit()
        assert isinstance(deliv_zip, str) and \
            (deliv_zip.isdigit() or len(deliv_zip) == 0)

        assert 0 <= int(barcode_id) % 10 <= 4, \
            'barcode id must end in 0-4 (and be 2-digit)'
        assert 0 <= int(barcode_id) <= 99, \
            'barcode id must be 2-digit (and end in 0-4)'
        self.__barcode_id = barcode_id

        assert 0 <= int(st_id) <= 999, 'Service Type ID must be 3-digit'
        self.__service_type_id = st_id

        mid_len = len(mailer_id)
        assert mid_len == 6 or mid_len == 9, 'Mailer id must be 6 or 9 digits'
        if mid_len == 9:
            assert  900000000 <= int(mailer_id) <= 999999999, \
                'Invalid mailer_id range'
        else:  # len == 6
            assert 0 <= int(mailer_id) <= 899999, 'Invalid mailer_id range'
        self.__mailer_id = mailer_id

        snum_len = len(serial_num)
        assert snum_len == 6 or snum_len == 9, \
            'Serial num must be 6 or 9 digits'
        if len(str(serial_num)) == 9:
            assert mid_len == 6, \
                'mailer id must be 6-digit when serial num is 9-digit'
        else:  # len == 6
            assert mid_len == 9, \
                'mailer id must be 9-digit when serial num is 6-digit'
        self.__serial_num = serial_num

        dzip_len = len(deliv_zip)
        assert any((dzip_len == 0, dzip_len == 5, \
                    dzip_len == 9, dzip_len == 11))
        self.__deliv_zip = deliv_zip

    @property
    def barcode_id(self):
        """Return barcode ID (string)"""
        return self.__barcode_id

    @property
    def service_type_id(self):
        """Return service type ID (string)"""
        return self.__service_type_id

    @property
    def mailer_id(self):
        """Return mailer ID (string)"""
        return self.__mailer_id

    @property
    def serial_num(self):
        """Return Serial Number (string)"""
        return self.__serial_num

    @property
    def deliv_zip(self):
        """Return delivery zip (string)"""
        return self.__deliv_zip

    @property
    def tracking(self):
        """Return tracking number (string)"""
        return self.barcode_id + self.service_type_id + self.mailer_id \
            + self.serial_num

    @property
    def routing(self):
        """Return routing number, aka zip (string)"""
        return self.deliv_zip

    def __str__(self):
        return self.tracking + self.routing


def encode(imb):
    """
    Encode Intelligent Mail Barcode to a string representing visual
    representation of the barcode.
    """
    assert isinstance(imb, IntelligentMailBarcode)
    # 1. Convert data fields to binary
    routing_len = len(imb.routing)
    if routing_len == 0:
        rc_val = 0
    elif routing_len == 5:
        rc_val = int(imb.routing) + 1
    elif routing_len == 9:
        rc_val = int(imb.routing) + 100001
    elif routing_len == 11:
        rc_val = int(imb.routing) + 1000100001  # 1,000,100,001
    rc_val *= 10
    rc_val += int(imb.tracking[0])
    rc_val *= 5
    rc_val += int(imb.tracking[1])

    for _ in imb.tracking[2:]:
        rc_val *= 10
        rc_val += int(_)

    # 2. 11-bit CRC on binary
    gen_poly = 0x0f35
    fcs = 0x07ff
    data = (rc_val >> 12 * 8) << 5
    for _ in range(2, 8):
        if (fcs ^ data) & 0x400:
            fcs = (fcs << 1) ^ gen_poly
        else:
            fcs = fcs << 1
        fcs &= 0x7ff
        data <<= 1
    for _ in range(1, 13):
        data = rc_val >> (12 - _) * 8
        data &= 0xff
        data <<= 3
        for _bit in range(8):
            if (fcs ^ data) & 0x400:
                fcs = (fcs << 1) ^ gen_poly
            else:
                fcs = fcs << 1
            fcs &= 0x7ff
            data <<= 1

    # 3. codeword generation
    rc_val, cw_j = divmod(rc_val, 636)
    rc_val, cw_i = divmod(rc_val, 1365)
    rc_val, cw_h = divmod(rc_val, 1365)
    rc_val, cw_g = divmod(rc_val, 1365)
    rc_val, cw_f = divmod(rc_val, 1365)
    rc_val, cw_e = divmod(rc_val, 1365)
    rc_val, cw_d = divmod(rc_val, 1365)
    rc_val, cw_c = divmod(rc_val, 1365)
    rc_val, cw_b = divmod(rc_val, 1365)
    assert 0 <= rc_val <= 658, 'Codeword conversion error during encoding'
    cw_a = rc_val

    # 4. codeword modification
    cw_j *= 2
    if (fcs >> 10 & 1):
        cw_a += 659

    # 5. codeword to 'character' conversion
    lut5 = _lookup_table(5, 1287)
    lut2 = _lookup_table(2, 78)

    char_list = []
    for cw in [cw_a, cw_b, cw_c, cw_d, cw_e, cw_f, cw_g, cw_h, cw_i, cw_j]:
        if cw <= 1286:
            cw_char = lut5[cw]
        elif 1287 <= cw <= 1364:
            cw_char = lut2[cw - 1287]
        else:
            print 'codeword > 1364, should not happen'
        char_list.append(cw_char)

    for i in range(10):
        if fcs & 1 << i:
            char_list[i] = char_list[i] ^ 0x1fff

    # 6. character to barcode conversion
    bar_table = _bar_construction_table()
    enc_str = ''
    for i in range(65):
        bar_map = bar_table[i]
        asc_index = ord(bar_map.asc_char) - ord('A')
        desc_index = ord(bar_map.desc_char) - ord('A')
        asc = char_list[asc_index] & 1 << int(bar_map.asc_bit)
        desc = char_list[desc_index] & 1 << int(bar_map.desc_bit)

        if asc and desc:
            enc_str += 'F'
        elif asc:
            enc_str += 'A'
        elif desc:
            enc_str += 'D'
        else:
            enc_str += 'T'

    return enc_str


def decode(encstr):
    """Decode 'ADTF' string and create IntelligentMailBarcode """
    return 'Not implemented'


def from_t_and_r(tracking_routing):
    """
    Create and return IM Barcode

    tracking_and_routing - string concatenation of tracking and routing
    """
    tracking = tracking_routing[:20]
    routing = tracking_routing[20:]
    bar_id = tracking[:2]
    st_id = tracking[2:5]
    if tracking[5] == '9':  # 9 digit mail id
        m_id = tracking[5:14]
        seq_num = tracking[14:20]
    else:
        m_id = tracking[5:11]
        seq_num = tracking[11:20]

    return IntelligentMailBarcode(bar_id, st_id, m_id, seq_num, routing)


def gimp_imb(curr_img, arg1, arg2):
    'Generates text for Barcode on new Layer'
    font = ['USPSIMBStandard Medium', 'USPSIMBCompact'][arg2]
    font_size = [16.0, 14.0][arg2]
    if set(arg1) == set('ADTF'):
        enc_str = arg1
    else:
        try:
            new_imb = from_t_and_r(arg1)
            enc_str = encode(new_imb)
        except StandardError as exc:
            pdb.gimp_message(repr(exc))

    #pdb.gimp_text_fontname(curr_img, -1, 0, 0, enc_str, 0, False, \
    #                       16.0, 0, 'USPSIMBCompact')
    pdb.gimp_message('arg2 : %s' % str(type(arg2)))
    txt_layer = \
    pdb.gimp_text_layer_new(curr_img, enc_str, font, font_size, 3)
    curr_img.add_layer(txt_layer)


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '-gimp':
        # presumably running in gimp
        try:
            from gimpfu import *  # @UnusedWildImport
        except ImportError as err:
            print err
            exit(1)

        register('im_barcode',
                 GIMP_BLURB,
                 GIMP_HELP,
                 GIMP_AUTHOR,
                 GIMP_COPYRIGHT,
                 GIMP_DATE,
                 "_Barcode",
                 '*',
                 [
                  (PF_IMAGE, 'curr_img', 'Which Image', None),
                  (PF_STRING, 'rt', 'Routing and Tracking code', None),
                  (PF_RADIO, 'radio', 'Font Option:', 0,
                   (("Standard", 0), ("Compact", 1)))
                  ],
                 [],
                 gimp_imb, menu="<Image>/Filters/Render/IMBarcode"
                 )
        main()
    else:
        parser = argparse.ArgumentParser(
                    description="Encode / Decode Intelligent Mail Barcodes",
                    epilog='\n')
        parser.add_argument('rt', metavar='RoutingTracking',
                        help='Unencoded routing/tracking or \'ADTF\' encoded',
                        nargs='+')
        args = parser.parse_args()
        inputs = args.rt
        for _i in inputs:
            if set('ADTF') == set(_i):
                decoded = decode(_i)
                print decoded
            else:
                my_imb = from_t_and_r(_i)
                adtf_encoded = encode(my_imb)
                print adtf_encoded
