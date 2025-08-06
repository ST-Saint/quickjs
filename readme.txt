The main documentation is in doc/quickjs.pdf or doc/quickjs.html.

To build qjs_sc: make qjs_sc

Usage: qjs_sc PATH_TO_BYTECODE_BINARY

Sample Output:

Read 26 bytes from /LLCT/resources/js/.bytecode/branch.bytecode:
61 00 00 B7 CB D3 EC 09 D4 11 63 00 00 0E EE 07 D5 11 63 00 00 0E 62 00 00 28
[0000:61]: set_loc_uninitialized += 3
[0003:B7]: push_0 += 1
[0004:CB]: put_loc0 += 1
[0005:D3]: get_arg0 += 1
[0006:EC]: if_false8 offset: 9, target 16
[0008:D4]: get_arg1 += 1
[0009:11]: dup += 1
[0010:63]: put_loc_check += 3
[0013:0E]: drop += 1
[0014:EE]: goto8 offset: 7, target 22
[0016:D5]: get_arg2 += 1
[0017:11]: dup += 1
[0018:63]: put_loc_check += 3
[0021:0E]: drop += 1
[0022:62]: get_loc_check += 3
[0025:28]: return += 1
Total instructions: 16
idom 25: 26
idom 22: 25
idom 21: 22
idom 18: 21
idom 17: 18
idom 16: 17
idom 6: 22
idom 5: 6
idom 4: 5
idom 3: 4
idom 0: 3
idom 14: 22
idom 13: 14
idom 10: 13
idom 9: 10
idom 8: 9
