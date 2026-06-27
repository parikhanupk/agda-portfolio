import ctypes
import os
from pathlib import Path



script_dir = Path(__file__).resolve().parent
lib_path = os.path.abspath(str(script_dir) + """/demo.so""")
agda_lib = ctypes.CDLL(lib_path)

agda_lib.hs_init.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
agda_lib.hs_init.restype = None
agda_lib.hs_exit.argtypes = []
agda_lib.hs_exit.restype = None

agda_lib.c_process.argtypes = [ctypes.c_char_p]
agda_lib.c_process.restype = ctypes.c_void_p

agda_lib.c_free_string.argtypes = [ctypes.c_void_p]
agda_lib.c_free_string.restype = None

def call_agda_process(lib, command):
    raw_ptr_address = lib.c_process(command)
    if raw_ptr_address:
        return ctypes.string_at(raw_ptr_address).decode('utf-8')
        lib.c_free_string(raw_ptr_address)
    else:
        return "Received a null pointer."

try:
    agda_lib.hs_init(None, None)
    ok, err = 0, 0
    for bits in range(1, 9):
        for c in range(2):
            for a in range(2 ** bits):
                for b in range(2 ** bits):
                    ra, rb = f"{a:0{bits}b}"[::-1], f"{b:0{bits}b}"[::-1]
                    rca_in = f"rca {ra} {rb} {c}".encode("utf-8")
                    rca_out = call_agda_process(agda_lib, rca_in)
                    if rca_out.startswith("Carry="):
                        rca_carry, rca_sum = rca_out.split(" ")
                        rca_carry, rca_sum = rca_carry[-1:], rca_sum[-bits:][::-1]
                        if ((int(rca_carry) * (2 ** bits)) + int(rca_sum, 2)) == (a + b + c):
                            ok += 1
                            print("OK:", "carry =", c, "+", a, "+", b, "=", rca_carry, rca_sum)
                        else:
                            err += 1
                            print("ERR:", "carry =", c, "+", a, "+", b, "=", rca_carry, rca_sum)
                    else:
                        print(rca_out)
    print(ok, "tests passed,", err, "tests failed")
finally:
    agda_lib.hs_exit()

