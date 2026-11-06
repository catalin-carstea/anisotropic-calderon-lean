import Calderon.ActualFiniteHarmonicModelAngularLinearBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma hasCoreAngularFirstOrderBounds_sub
    (A Astar B Bstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (CA CB : ℝ) (x : R3)
    (hA : HasCoreAngularFirstOrderBounds hO hD A Astar CA x)
    (hB : HasCoreAngularFirstOrderBounds hO hD B Bstar CB x) :
    HasCoreAngularFirstOrderBounds hO hD (A-B) (Astar-Bstar) (CA+CB) x := by
  rw [_root_.sub_eq_add_neg A B, _root_.sub_eq_add_neg Astar Bstar]
  exact hasCoreAngularFirstOrderBounds_add hO hD
    A Astar (-B) (-Bstar) CA CB x hA (hasCoreAngularFirstOrderBounds_neg hO hD B Bstar CB x hB)

lemma hasCoreAngularFirstOrderBounds_ite
    (P : Prop) [Decidable P] (T Tstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (C : ℝ) (x : R3) (hT : HasCoreAngularFirstOrderBounds hO hD T Tstar C x) :
    HasCoreAngularFirstOrderBounds hO hD (if P then T else 0) (if P then Tstar else 0) C x := by
  by_cases hP : P
  · simpa only [if_pos hP] using hT
  · simpa only [if_neg hP] using hasCoreAngularFirstOrderBounds_mono hO hD 0 0 0 C x
      (hasCoreAngularFirstOrderBounds_zero hO hD x) hT.1

lemma hasCoreAngularFirstOrderBounds_commutator_of_commute
    (T U : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hTU : Commute T U) (C : ℝ) (hC : 0 ≤ C) (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD (commutator T U) 0 C x := by
  have he : commutator T U = 0 := sub_eq_zero.mpr hTU.eq
  rw [he]
  exact hasCoreAngularFirstOrderBounds_mono hO hD 0 0 0 C x
    (hasCoreAngularFirstOrderBounds_zero hO hD x) hC

lemma hasCoreAngularFirstOrderBounds_commutator_swap
    (T U V : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (C : ℝ) (x : R3)
    (h : HasCoreAngularFirstOrderBounds hO hD (commutator T U) V C x) :
    HasCoreAngularFirstOrderBounds hO hD (commutator U T) (-V) C x := by
  have he : commutator U T = -commutator T U := by
    change U*T-T*U = -(T*U-U*T)
    abel
  rw [he]
  exact hasCoreAngularFirstOrderBounds_neg hO hD (commutator T U) V C x h

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
