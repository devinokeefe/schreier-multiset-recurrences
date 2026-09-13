import Main
import Examples

-- The literal counted family and the closed target.
#print SchreierQ3.ambient
#print SchreierQ3.Schreier3
#print SchreierQ3.family
#print SchreierQ3.a
#print SchreierQ3.InitialValues
set_option pp.coercions.types true in
#print SchreierQ3.Recurrence
#print SchreierQ3.MainClaim
#check SchreierQ3.main

-- The minimum and inverse correspondences include their required domains.
#check SchreierQ3.schreier3_iff_at_minimum
#check SchreierQ3.decode_encode
#check SchreierQ3.encode_decode
#check SchreierQ3.count_bridge

-- Transitive logical dependencies, including the independent finite count.
#print axioms SchreierQ3.mem_compositions
#print axioms SchreierQ3.c_step
#print axioms SchreierQ3.decode_encode
#print axioms SchreierQ3.encode_decode
#print axioms SchreierQ3.count_bridge
#print axioms SchreierQ3.direct_initial_values
#print axioms SchreierQ3.main
