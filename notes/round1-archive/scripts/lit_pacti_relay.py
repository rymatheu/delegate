from pacti.contracts import PolyhedralIoContract as C
top = C.from_strings(input_vars=["r"], output_vars=["d"],
        assumptions=["r <= 1", "-r <= 1"], guarantees=["d - r <= 0.5", "r - d <= 0.5"])
# 1) Radio with trivial contract (no component contracts available)
radio_triv = C.from_strings(input_vars=["r"], output_vars=["m"], assumptions=[], guarantees=[])
for name, rc in [("trivial radio", radio_triv),
                 ("band radio |m-r|<=0.2", C.from_strings(input_vars=["r"], output_vars=["m"], assumptions=["r<=1","-r<=1"], guarantees=["m - r <= 0.2","r - m <= 0.2"]))]:
    try:
        q = top.quotient(rc)
        print(name, "-> quotient (Display):\n", q)
    except Exception as e:
        print(name, "-> quotient FAILED:", type(e).__name__, e)
# 2) Display trivial, quotient for Radio
disp_triv = C.from_strings(input_vars=["m"], output_vars=["d"], assumptions=[], guarantees=[])
try:
    print("trivial display -> quotient (Radio):\n", top.quotient(disp_triv))
except Exception as e:
    print("trivial display -> quotient FAILED:", type(e).__name__, e)
