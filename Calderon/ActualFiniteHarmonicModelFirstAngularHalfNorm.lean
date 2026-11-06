import Calderon.ActualFiniteHarmonicModelHalfWeightSumAction

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  BoundedAngularShift ActualReferenceDDSpectralTransport
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev firstAngularHalfNormFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] firstAngularHalfNormFunction

lemma norm_coreWeight_half_first_angular_le
    (hF : SphereFischerInner) (M N : SphereL2 →L[ℝ] SphereL2)
    (hM : PreservesSphereSpectralGraphs hO hD M)
    (A F : smoothCompactFiniteSphereCore hO hD) (c : Fin 3 → ℝ) (x : R3)
    (B J : ℝ) (hJ : 0 ≤ J) (hN : ‖N‖ ≤ B) (hc : ∀ a, |c a| ≤ J)
    (hMN : N = M+∑ a : Fin 3, c a •
      (normalizedDerivative hF hO hD a+normalizedRaising hF hO hD a))
    (hA : A x = M (coreWeightOperator hO hD (besselWeight 1) F x)+
      ∑ a : Fin 3, c a • (coreDerivative hO hD hF a F x+coreRaising hO hD hF a F x)) :
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) A x‖ ≤
      (B+J*((∑ a : Fin 3, ‖normalizedDerivative hF hO hD a+normalizedRaising hF hO hD a‖)+
        3*(2+2*(2 : ℝ)^(1/2 : ℝ))))*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  classical
  let T (a : Fin 3) := normalizedDerivative hF hO hD a+normalizedRaising hF hO hD a
  let U (a : Fin 3) := coreDerivative hO hD hF a F+coreRaising hO hD hF a F
  let b : ℝ := 2+2*(2 : ℝ)^(1/2 : ℝ)
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hU (a : Fin 3) :
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (U a) x‖ ≤
        b*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
    change ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (coreDerivative hO hD hF a F+coreRaising hO hD hF a F) x‖ ≤ _
    simp only [map_add,Submodule.coe_add,Pi.add_apply]
    exact (norm_add_le _ _).trans (by
      have hh := add_le_add (norm_coreWeight_half_derivative_le hO hD hF a F x)
        (norm_coreWeight_half_raising_le hO hD hF a F x)
      simpa only [b,add_mul,mul_assoc] using hh)
  have hMn : ‖M‖ ≤ B+J*∑ a : Fin 3, ‖T a‖ := by
    have he : M = N-∑ a : Fin 3, c a • T a := by rw [hMN]; dsimp only [T]; abel
    rw [he]
    calc
      _ ≤ ‖N‖+‖∑ a : Fin 3, c a • T a‖ := norm_sub_le _ _
      _ ≤ B+∑ a : Fin 3, ‖c a • T a‖ := add_le_add hN (norm_sum_le _ _)
      _ ≤ B+∑ a : Fin 3, J*‖T a‖ := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro a ha
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hc a) (norm_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have hs : (∑ a : Fin 3, |c a| * b) ≤ 3*J*b := by
    calc
      _ ≤ ∑ a : Fin 3, J*b := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (hc a) hb)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  have ht := norm_coreWeight_half_le_preserving_add_sum hO hD M hM A F U c
    (fun _ => b) x hA hU
  calc
    _ ≤ (‖M‖+∑ a : Fin 3, |c a| * b)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := ht
    _ ≤ ((B+J*∑ a : Fin 3, ‖T a‖)+3*J*b)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ :=
      mul_le_mul_of_nonneg_right (add_le_add hMn hs) (norm_nonneg _)
    _ = _ := by dsimp only [T,b]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
