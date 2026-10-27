import Sail

section PrimitiveTests

open Sail

-- `set_slice_int len n lo x` replaces bits `[lo, lo + len)` of `n` and keeps the rest.
-- Expected values are those of `set_slice_int` in Sail's lib/sail.c.
#guard set_slice_int 4 0 0 0xF#4 == 15
#guard set_slice_int 4 0x100 0 0x3#4 == 0x103
#guard set_slice_int 8 0 8 0xFF#8 == 0xFF00
#guard set_slice_int 8 (-1) 0 0x00#8 == -256
#guard set_slice_int 4 (-1) 4 0x0#4 == -241
#guard set_slice_int 8 0x12345678 8 0xAB#8 == 0x1234AB78
#guard set_slice_int 0 5 3 0#0 == 5

-- `valid_hex_bits` and `valid_dec_bits` follow Sail's lib/sail.c.
#guard valid_hex_bits 8 "0xff"
#guard valid_hex_bits 8 "0x00FF"
#guard valid_hex_bits 3 "0x7"
#guard !valid_hex_bits 3 "0x8"
#guard !valid_hex_bits 3 "0x10"
#guard !valid_hex_bits 8 "0x1ff"
#guard !valid_hex_bits 12 "0x1001"
#guard !valid_hex_bits 8 "1234"
#guard !valid_hex_bits 8 "0x"
#guard !valid_hex_bits 8 "0xg"
#guard !valid_hex_bits 8 "0XFF"
#guard valid_dec_bits 4 "15"
#guard valid_dec_bits 4 "0015"
#guard !valid_dec_bits 4 "16"
#guard !valid_dec_bits 4 "99"
#guard !valid_dec_bits 4 ""
#guard !valid_dec_bits 4 "-1"

end PrimitiveTests
