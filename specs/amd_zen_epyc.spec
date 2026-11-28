# AMD Zen 1..5 / EPYC 7001..9005 Architectural Specification (7-bit ASCII)
# Format: [profile_name] followed by key=value pairs.
# All cache sizes are per-core (L1D, L2) or per-CCX/CCD (L3, 3D V-Cache).

[zen1_naples]
family=23
models=1..15
l1d_kib=32
l1d_ways=8
l2_kib=512
l3_ccx_mib=8
l3_3dv_mib=0
ccx_cores=4
line_bytes=64
simd=avx2_128x2
vec_regs=16
vec_bits=256
native_pipe_bits=128

[zen2_rome]
family=23
models=49,113,96,144
l1d_kib=32
l1d_ways=8
l2_kib=512
l3_ccx_mib=16
l3_3dv_mib=0
ccx_cores=4
line_bytes=64
simd=avx2
vec_regs=16
vec_bits=256
native_pipe_bits=256

[zen3_milan]
family=25
models=1,33,80
l1d_kib=32
l1d_ways=8
l2_kib=512
l3_ccx_mib=32
l3_3dv_mib=96
ccx_cores=8
line_bytes=64
simd=avx2
vec_regs=16
vec_bits=256
native_pipe_bits=256

[zen4_genoa]
family=25
models=17,97,116
l1d_kib=32
l1d_ways=8
l2_kib=1024
l3_ccx_mib=32
l3_3dv_mib=96
ccx_cores=8
line_bytes=64
simd=avx512_256x2
vec_regs=32
vec_bits=512
native_pipe_bits=256

[zen4c_bergamo]
family=25
models=24,160
l1d_kib=32
l1d_ways=8
l2_kib=1024
l3_ccx_mib=16
l3_3dv_mib=0
ccx_cores=8
line_bytes=64
simd=avx512_256x2
vec_regs=32
vec_bits=512
native_pipe_bits=256

[zen5_turin]
family=26
models=2,17,68
l1d_kib=48
l1d_ways=12
l2_kib=1024
l3_ccx_mib=32
l3_3dv_mib=96
ccx_cores=8
line_bytes=64
simd=avx512_512
vec_regs=32
vec_bits=512
native_pipe_bits=512
