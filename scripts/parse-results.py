#!/usr/bin/env python
# coding: utf-8

# In[ ]:


import re
import sys


# In[ ]:


# choose between utils or core
# SERIES = "utils"
# SERIES = "core"
SERIES = sys.argv[1]


# In[ ]:


bmrks = None
if SERIES == "utils":
    bmrks = [
        "AND@gates.circom",
        "BabyAdd@babyjub.circom",
        "BabyDbl@babyjub.circom",
        "BabyPbk@babyjub.circom",
        "BinSub@binsub.circom",
        "BinSum@binsum.circom",
        "BitElementMulAny@escalarmulany.circom",
        "Bits2Num_strict@bitify.circom",
        "Bits2Num@bitify.circom",
        "Bits2Point_Strict@pointbits.circom",
        "CompConstant@compconstant.circom",
        "Decoder@multiplexer.circom",
        "Edwards2Montgomery@montgomery.circom",
        "EscalarMulAny@escalarmulany.circom",
        "EscalarProduct@multiplexer.circom",
        "GreaterEqThan@comparators.circom",
        "GreaterThan@comparators.circom",
        "IsEqual@comparators.circom",
        "IsZero@comparators.circom",
        "LessEqThan@comparators.circom",
        "LessThan@comparators.circom",
        "MiMC7@mimc.circom",
        "MiMCFeistel@mimcsponge.circom",
        "MiMCSponge@mimcsponge.circom",
        "Montgomery2Edwards@montgomery.circom",
        "MontgomeryAdd@montgomery.circom",
        "MontgomeryDouble@montgomery.circom",
        "MultiAND@gates.circom",
        "MultiMiMC7@mimc.circom",
        "MultiMux1@mux1.circom",
        "MultiMux2@mux2.circom",
        "MultiMux3@mux3.circom",
        "MultiMux4@mux4.circom",
        "Multiplexer@multiplexer.circom",
        "Multiplexor2@escalarmulany.circom",
        "Mux1@mux1.circom",
        "Mux2@mux2.circom",
        "Mux3@mux3.circom",
        "Mux4@mux4.circom",
        "NAND@gates.circom",
        "NOR@gates.circom",
        "NOT@gates.circom",
        "Num2Bits_strict@bitify.circom",
        "Num2Bits@bitify.circom",
        "Num2BitsNeg@bitify.circom",
        "OR@gates.circom",
        "Pedersen@pedersen_old.circom",
        "Pedersen@pedersen.circom",
        "Point2Bits_Strict@pointbits.circom",
        "Poseidon@poseidon.circom",
        "Segment@pedersen.circom",
        "SegmentMulAny@escalarmulany.circom",
        "SegmentMulFix@escalarmulfix.circom",
        "Sigma@poseidon.circom",
        "Sign@sign.circom",
        "Switcher@switcher.circom",
        "Window4@pedersen.circom",
        "WindowMulFix@escalarmulfix.circom",
        "XOR@gates.circom",
    ]
else:
    bmrks = [
        "AND@gates@circomlib.circom",
        "BabyAdd@babyjub@circomlib.circom",
        "BabyDbl@babyjub@circomlib.circom",
        "BabyPbk@babyjub@circomlib.circom",
        "BinSub@binsub@circomlib_16.circom",
        "BinSum@binsum@circomlib_32_2.circom",
        "BinSum@binsum@circomlib_32_5.circom",
        "BitElementMulAny@escalarmulany@circomlib.circom",
        "Bits2Num@bitify@circomlib_1.circom",
        "Bits2Num@bitify@circomlib_128.circom",
        "Bits2Num@bitify@circomlib_16.circom",
        "Bits2Num@bitify@circomlib_253.circom",
        "Bits2Num@bitify@circomlib_254.circom",
        "Bits2Num@bitify@circomlib_256.circom",
        "Bits2Num@bitify@circomlib_32.circom",
        "Bits2Num@bitify@circomlib_64.circom",
        "Bits2Num@bitify@circomlib_8.circom",
        "Bits2Num_strict@bitify@circomlib.circom",
        "Bits2Point@pointbits@circomlib.circom",
        "Bits2Point_Strict@pointbits@circomlib.circom",
        "Edwards2Montgomery@montgomery@circomlib.circom",
        "GreaterEqThan@comparators@circomlib_16.circom",
        "GreaterEqThan@comparators@circomlib_32.circom",
        "GreaterEqThan@comparators@circomlib_8.circom",
        "GreaterThan@comparators@circomlib_16.circom",
        "GreaterThan@comparators@circomlib_32.circom",
        "GreaterThan@comparators@circomlib_8.circom",
        "IsEqual@comparators@circomlib.circom",
        "IsZero@comparators@circomlib.circom",
        "LessEqThan@comparators@circomlib_16.circom",
        "LessEqThan@comparators@circomlib_32.circom",
        "LessEqThan@comparators@circomlib_8.circom",
        "Main@main@circomlib.circom",
        "Montgomery2Edwards@montgomery@circomlib.circom",
        "MontgomeryAdd@montgomery@circomlib.circom",
        "MontgomeryDouble@montgomery@circomlib.circom",
        "Multiplexor2@escalarmulany@circomlib.circom",
        "Mux1@mux1@circomlib.circom",
        "Mux2@mux2@circomlib.circom",
        "Mux3@mux3@circomlib.circom",
        "Mux4@mux4@circomlib.circom",
        "NAND@gates@circomlib.circom",
        "NOR@gates@circomlib.circom",
        "NOT@gates@circomlib.circom",
        "Num2Bits@bitify@circomlib_1.circom",
        "Num2Bits@bitify@circomlib_128.circom",
        "Num2Bits@bitify@circomlib_16.circom",
        "Num2Bits@bitify@circomlib_253.circom",
        "Num2Bits@bitify@circomlib_254.circom",
        "Num2Bits@bitify@circomlib_256.circom",
        "Num2Bits@bitify@circomlib_32.circom",
        "Num2Bits@bitify@circomlib_64.circom",
        "Num2Bits@bitify@circomlib_8.circom",
        "Num2BitsNeg@bitify@circomlib_1.circom",
        "Num2BitsNeg@bitify@circomlib_128.circom",
        "Num2BitsNeg@bitify@circomlib_16.circom",
        "Num2BitsNeg@bitify@circomlib_253.circom",
        "Num2BitsNeg@bitify@circomlib_254.circom",
        "Num2BitsNeg@bitify@circomlib_256.circom",
        "Num2BitsNeg@bitify@circomlib_32.circom",
        "Num2BitsNeg@bitify@circomlib_64.circom",
        "Num2BitsNeg@bitify@circomlib_8.circom",
        "Num2Bits_strict@bitify@circomlib.circom",
        "OR@gates@circomlib.circom",
        "Pedersen@pedersen@circomlib_1.circom",
        "Pedersen@pedersen@circomlib_128.circom",
        "Pedersen@pedersen@circomlib_16.circom",
        "Pedersen@pedersen@circomlib_253.circom",
        "Pedersen@pedersen@circomlib_254.circom",
        "Pedersen@pedersen@circomlib_256.circom",
        "Pedersen@pedersen@circomlib_32.circom",
        "Pedersen@pedersen@circomlib_64.circom",
        "Pedersen@pedersen@circomlib_8.circom",
        "Pedersen@pedersen_old@circomlib_1.circom",
        "Pedersen@pedersen_old@circomlib_128.circom",
        "Pedersen@pedersen_old@circomlib_16.circom",
        "Pedersen@pedersen_old@circomlib_253.circom",
        "Pedersen@pedersen_old@circomlib_254.circom",
        "Pedersen@pedersen_old@circomlib_256.circom",
        "Pedersen@pedersen_old@circomlib_32.circom",
        "Pedersen@pedersen_old@circomlib_64.circom",
        "Pedersen@pedersen_old@circomlib_8.circom",
        "Point2Bits@pointbits@circomlib.circom",
        "Point2Bits_Strict@pointbits@circomlib.circom",
        "SMTHash1@smthash_mimc@circomlib.circom",
        "SMTHash1@smthash_poseidon@circomlib.circom",
        "SMTHash2@smthash_mimc@circomlib.circom",
        "SMTHash2@smthash_poseidon@circomlib.circom",
        "SMTProcessorLevel@smtprocessorlevel@circomlib.circom",
        "SMTProcessorSM@smtprocessorsm@circomlib.circom",
        "SMTVerifierLevel@smtverifierlevel@circomlib.circom",
        "SMTVerifierSM@smtverifiersm@circomlib.circom",
        "Sha256_2@sha256_2@circomlib.circom",
        "Sha256compression@sha256compression@circomlib.circom",
        "Sigma@poseidon@circomlib.circom",
        "Sigma@poseidon_old@circomlib.circom",
        "SigmaPlus@sigmaplus@circomlib.circom",
        "Sign@sign@circomlib.circom",
        "Switcher@switcher@circomlib.circom",
        "T1@t1@circomlib.circom",
        "T2@t2@circomlib.circom",
        "Window4@pedersen@circomlib.circom",
        "WindowMulFix@escalarmulfix@circomlib.circom",
        "XOR@gates@circomlib.circom",
    ]


# In[ ]:


# parse stats
with open("../logs/compile-{}.log".format(SERIES), "r") as f:
    raw = f.read()
    ll = raw.split("=================== ")
    ll = list(filter(lambda p:len(p)>0, ll))

stats = {}
for p in ll:
    pname = p[:p.index(":")]
    # print("# processing {}".format(pname))
    if pname not in bmrks:
        # print("# skipping {}".format(pname))
        continue
    re_nlcnst = int(re.search(r"\nnon-linear constraints: (.*)\n", p).group(1))
    re_lcnst = int(re.search(r"\nlinear constraints: (.*)\n", p).group(1))
    re_prvin = int(re.search(r"\nprivate inputs: (.*)\n", p).group(1))
    re_pubin = int(re.search(r"\npublic inputs: (.*)\n", p).group(1))
    re_prvout = int(re.search(r"\nprivate outputs: (.*)\n", p).group(1))
    re_pubout = int(re.search(r"\npublic outputs: (.*)\n", p).group(1))
    re_wires = int(re.search(r"\nwires: (.*)\n", p).group(1))
    stats[pname] = {}
    stats[pname]["non-linear constraints"] = re_nlcnst
    stats[pname]["linear constraints"] = re_lcnst
    stats[pname]["total constraints"] = re_nlcnst + re_lcnst
    stats[pname]["private inputs"] = re_prvin
    stats[pname]["private inputs"] = re_pubin
    stats[pname]["total inputs"] = re_prvin + re_pubin
    stats[pname]["private outputs"] = re_prvout
    stats[pname]["public outputs"] = re_pubout
    stats[pname]["total outputs"] = re_prvout + re_pubout
    stats[pname]["wires"] = re_wires
    stats[pname]["witness"] = re_wires - re_prvin - re_pubin - re_prvout - re_pubout
    cat = None
    if stats[pname]["total constraints"]<100:
        cat = "small"
    elif stats[pname]["total constraints"]>=100 and stats[pname]["total constraints"]<1000:
        cat = "medium"
    else:
        cat = "large"
    stats[pname]["cat"] = cat


# ## print Table 1, "circomlib-SERIES" part

# In[ ]:


# compute row "circomlib-SERIES" of Table 1
all_cnst = [stats[p]["total constraints"] for p in stats.keys()]
avg_cnst = round(sum(all_cnst)/len(all_cnst))
all_out = [stats[p]["total outputs"] for p in stats.keys()]
avg_out = round(sum(all_out)/len(all_out))

print('Table 1, "circomlib-{}" part'.format(SERIES))
TEMPLATE = "{:^15} | {:^10} | {:^20} | {:^20}"
print(TEMPLATE.format("Benchmark Set", "# circuits", "Avg. # constraints", "Avg. # output signals"))
print(TEMPLATE.format("circomlib-{}".format(SERIES), len(stats), avg_cnst, avg_out))


# In[ ]:


# parse time
with open("../logs/full-{}.log".format(SERIES), "r") as f:
    raw = f.read()
    for fn in bmrks:
        fn0 = fn.replace(".circom", ".r1cs")
        sp = raw.find(fn0)
        s0 = raw.find("elapsed: ", sp)
        ss = raw.find("seconds", s0)
        t = int(raw[s0+len("elapsed: "):ss])
        stats[fn]["time"] = t

# self check
for p in stats.keys():
    if "time" not in stats[p]:
        print("# panic: time for {} doesn't exist, check your experiment again!".format(p))


# In[ ]:


# parse result
for ff in bmrks:
    with open("../logs/full-{}/{}.log".format(SERIES, ff.replace(".circom","")),"r") as f:
        raw = f.read()
        if "# weak uniqueness: unsafe" in raw:
            stats[ff]["res"] = "unsafe"
        elif "# weak uniqueness: safe" in raw:
            stats[ff]["res"] = "safe"
        elif "# weak uniqueness: unknown" in raw:
            stats[ff]["res"] = "unknown"
        else:
            stats[ff]["res"] = "unknown"

# self check
for p in stats.keys():
    if "res" not in stats[p]:
        print("# panic: result data for {} doesn't exist, check your experiment again!".format(p))


# In[ ]:


def compute_table2(cat):

    cat_in = [stats[p]["total inputs"] for p in stats.keys() if cat == "overall" or stats[p]["cat"] == cat]
    avg_cat_in = round(sum(cat_in)/len(cat_in))

    cat_out = [stats[p]["total outputs"] for p in stats.keys() if cat == "overall" or stats[p]["cat"] == cat]
    avg_cat_out = round(sum(cat_out)/len(cat_out))

    cat_witness = [stats[p]["witness"] for p in stats.keys() if cat == "overall" or stats[p]["cat"] == cat]
    avg_cat_witness = round(sum(cat_witness)/len(cat_witness))

    cat_wires = [stats[p]["wires"] for p in stats.keys() if cat == "overall" or stats[p]["cat"] == cat]
    avg_cat_wires = round(sum(cat_wires)/len(cat_wires))

    cat_lcnst = [stats[p]["linear constraints"] for p in stats.keys() if cat == "overall" or stats[p]["cat"] == cat]
    avg_cat_lcnst = round(sum(cat_lcnst)/len(cat_lcnst))

    cat_nlcnst = [stats[p]["non-linear constraints"] for p in stats.keys() if cat == "overall" or stats[p]["cat"] == cat]
    avg_cat_nlcnst = round(sum(cat_nlcnst)/len(cat_nlcnst))

    cat_cnst = [stats[p]["total constraints"] for p in stats.keys() if cat == "overall" or stats[p]["cat"] == cat]
    avg_cat_cnst = round(sum(cat_cnst)/len(cat_cnst))

    subkeys = [p for p in stats.keys() if cat == "overall" or stats[p]["cat"] == cat]

    # need to exclude timeouts
    cat_time = [stats[p]["time"] for p in stats.keys() if (cat == "overall" or stats[p]["cat"] == cat) and (stats[p]["res"] == "safe" or stats[p]["res"] == "unsafe") and stats[p]["time"] < 600]
    avg_cat_time = round(sum(cat_time)/len(cat_time))

    cat_check = [stats[p]["res"] for p in stats.keys() if (cat == "overall" or stats[p]["cat"] == cat) and stats[p]["res"] == "safe"]

    cat_cross = [stats[p]["res"] for p in stats.keys() if (cat == "overall" or stats[p]["cat"] == cat) and stats[p]["res"] == "unsafe"]
    if cat == "overall" or cat == "small":
        # +1 for the additional "BitElementMulAny@escalarmulany.r1cs" solved by counter-example procedure
        if SERIES == "utils":
            cat_cross.append(stats["BitElementMulAny@escalarmulany.circom"])
        if SERIES == "core":
            cat_cross.append(stats["BitElementMulAny@escalarmulany@circomlib.circom"])

    TEMPLATE = "{:^20} | {:^5}"
    print(TEMPLATE.format("in", avg_cat_in))
    print(TEMPLATE.format("out", avg_cat_out))
    print(TEMPLATE.format("witness", avg_cat_witness))
    print(TEMPLATE.format("total (variables)", avg_cat_wires))
    print()
    print(TEMPLATE.format("linear", avg_cat_lcnst))
    print(TEMPLATE.format("non-linear", avg_cat_nlcnst))
    print(TEMPLATE.format("total (constraints)", avg_cat_cnst))
    print()
    print(TEMPLATE.format("Total (#)", len(subkeys)))
    print(TEMPLATE.format("Avg. Time (s)", avg_cat_time))
    print(TEMPLATE.format("check (#)", len(cat_check)))
    print(TEMPLATE.format("cross (#)", len(cat_cross)))
    print(TEMPLATE.format("Solved (%)", (len(cat_check) + len(cat_cross)) / len(subkeys)))


# ## print Table 2, "circomlib-SERIES" part

# In[ ]:


# compute column of "circomlib-SERIES" - "small" in Table 2
print('------> Table 2, "circomlib-{}" part, "small"'.format(SERIES))
compute_table2("small")


# In[ ]:


# compute column of "circomlib-SERIES" - "medium" in Table 2
print('------> Table 2, "circomlib-{}" part, "medium"'.format(SERIES))
compute_table2("medium")


# In[ ]:


# compute column of "circomlib-SERIES" - "large" in Table 2
print('------> Table 2, "circomlib-{}" part, "large"'.format(SERIES))
compute_table2("large")


# In[ ]:


# compute column of "circomlib-SERIES" - "overall" in Table 2
print('------> Table 2, "circomlib-{}" part, "overall"'.format(SERIES))
compute_table2("overall")


# In[ ]:


# parse result for ucp-SERIES
for ff in bmrks:
    with open("../logs/ucp-{}/{}.log".format(SERIES, ff.replace(".circom","")),"r") as f:
        raw = f.read()
        if "# weak uniqueness: unsafe" in raw:
            stats[ff]["ucp_res"] = "unsafe"
        elif "# weak uniqueness: safe" in raw:
            stats[ff]["ucp_res"] = "safe"
        elif "# weak uniqueness: unknown" in raw:
            stats[ff]["ucp_res"] = "unknown"
        else:
            stats[ff]["ucp_res"] = "unknown"

# self check
for p in stats.keys():
    if "ucp_res" not in stats[p]:
        print("# panic: ucp result data for {} doesn't exist, check your experiment again!".format(p))


# In[ ]:


# parse result for smt-SERIES
for ff in bmrks:
    with open("../logs/smt-{}/{}.log".format(SERIES, ff.replace(".circom","")),"r") as f:
        raw = f.read()
        if "# weak uniqueness: unsafe" in raw:
            stats[ff]["smt_res"] = "unsafe"
        elif "# weak uniqueness: safe" in raw:
            stats[ff]["smt_res"] = "safe"
        elif "# weak uniqueness: unknown" in raw:
            stats[ff]["smt_res"] = "unknown"
        else:
            stats[ff]["smt_res"] = "unknown"

# self check
for p in stats.keys():
    if "smt_res" not in stats[p]:
        print("# panic: smt result data for {} doesn't exist, check your experiment again!".format(p))


# ## print Figure 11, "circomlib-SERIES" part

# In[ ]:


# compute solved% for full-SERIES
full_check = [stats[p]["res"] for p in stats.keys() if stats[p]["res"] == "safe"]
full_cross = [stats[p]["res"] for p in stats.keys() if stats[p]["res"] == "unsafe"]
# +1 for the additional "BitElementMulAny@escalarmulany.r1cs" solved by counter-example procedure
if SERIES == "utils":
    full_cross.append(stats["BitElementMulAny@escalarmulany.circom"])
if SERIES == "core":
    full_cross.append(stats["BitElementMulAny@escalarmulany@circomlib.circom"])
full_percentage = (len(full_check) + len(full_cross)) / len(stats)

# compute solved% for ucp-SERIES
ucp_check = [stats[p]["ucp_res"] for p in stats.keys() if stats[p]["ucp_res"] == "safe"]
ucp_cross = [stats[p]["ucp_res"] for p in stats.keys() if stats[p]["ucp_res"] == "unsafe"]
ucp_percentage = (len(ucp_check) + len(ucp_cross)) / len(stats)

# compute solved% for smt-SERIES
smt_check = [stats[p]["smt_res"] for p in stats.keys() if stats[p]["smt_res"] == "safe"]
smt_cross = [stats[p]["smt_res"] for p in stats.keys() if stats[p]["smt_res"] == "unsafe"]
smt_percentage = (len(smt_check) + len(smt_cross)) / len(stats)

print('------> Figure 11, "circomlib-{}" part'.format(SERIES))
print("FULL: {:.2}\nUCP: {:.2}\nSMT: {:.2}".format(full_percentage, ucp_percentage, smt_percentage))


# In[ ]:





# In[ ]:





# In[ ]:





# In[ ]:




