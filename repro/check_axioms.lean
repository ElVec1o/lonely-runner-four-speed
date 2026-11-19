/-
# check_axioms.lean : print the axioms of the headline theorems of the four-speed spectrum.  Builds NOTHING.

Run through `check_axioms.sh` (which runs `lake env lean check_axioms.lean` and checks the printout).
It only needs the .olean files of the 103 modules of MANIFEST.tsv (it imports the root module of the closure).

Every `#print axioms` below must print exactly the three standard axioms [propext, Classical.choice, Quot.sound],
except the planted control at the end, which must print `sorryAx` (it proves that a `sorry` anywhere below a
theorem would be visible in this printout).  No `sorry`, no `native_decide`, no extra axiom is used in the chain.
-/
import LRSpectrumFull.L4S5.FourSpeed

/-! ## The statements, as Lean prints them (read these against the English statement in README.md) -/

#check @LRSpectrumFull.L4S5.four_speed_spectrum
#check @LRSpectrumFull.L4S5.four_speed_attained
#check @LRSpectrumFull.L4S5.four_speed_spectrum_iff
#check @LRSpectrumFull.L4S5.tree_complete4_real
#check @LRSpectrumFull.L4S5.lines_all
#check @LRSpectrumFull.L4S5.streamHyp4_real
#check @LRSpectrumFull.L4Tail.ML_1_3_4_14
#print LRSpectrumFull.ML
#print LRSpectrumFull.nearestIntDist

/-! ## Axioms: the three headline theorems -/

#print axioms LRSpectrumFull.L4S5.four_speed_spectrum
#print axioms LRSpectrumFull.L4S5.four_speed_attained
#print axioms LRSpectrumFull.L4S5.four_speed_spectrum_iff

/-! ## Axioms: the certificate chain (hypothesis-free) and the glue -/

#print axioms LRSpectrumFull.L4S5.treeThm_real
#print axioms LRSpectrumFull.L4S5.tree_complete4_real
#print axioms LRSpectrumFull.L4S5.lines_all
#print axioms LRSpectrumFull.L4S5.streamHyp4_real
#print axioms LRSpectrumFull.L4S5.leafLinesB_sound
#print axioms LRSpectrumFull.L4S5.four_speed_spectrum_of_tree
#print axioms LRSpectrumFull.L4S4.tree_complete4
#print axioms LRSpectrumFull.L4S3.exists_flag_accepted

/-! ## Axioms: the two infinite tails, the sporadic value, the normal form -/

#print axioms LRSpectrumFull.L4Tail.U1_ge_quarter
#print axioms LRSpectrumFull.L4Tail.U1_exc_exact
#print axioms LRSpectrumFull.L4Tail.U1_spectrum
#print axioms LRSpectrumFull.L4Tail.U2_exact
#print axioms LRSpectrumFull.L4Tail.U2_spectrum
#print axioms LRSpectrumFull.L4Tail.U2_occurs_odd
#print axioms LRSpectrumFull.L4Tail.four_occurs
#print axioms LRSpectrumFull.L4Tail.four_tails_of_torus
#print axioms LRSpectrumFull.L4Tail.crit_torus_list
#print axioms LRSpectrumFull.L4Tail.ML_1_3_4_14

/-! ## Axioms: the consequence-level controls of FourSpeed.lean -/

#print axioms LRSpectrumFull.L4S5.ctl_not_one_sixth
#print axioms LRSpectrumFull.L4S5.ctl_not_three_fourteenths
#print axioms LRSpectrumFull.L4S5.ctl_sporadic_not_fifth

/-! ## NEGATIVE CONTROL (must print sorryAx; check_axioms.sh requires it) -/

theorem check_axioms_planted_sorry : (1 : Nat) = 2 := by sorry
theorem check_axioms_planted_sorry_user : (2 : Nat) = 3 := by
  have := check_axioms_planted_sorry
  omega

#print axioms check_axioms_planted_sorry
#print axioms check_axioms_planted_sorry_user
