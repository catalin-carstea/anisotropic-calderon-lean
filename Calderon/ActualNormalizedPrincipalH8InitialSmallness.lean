import Calderon.ExteriorAffineMetricNormalization
import Calderon.CompactZeroSliceNormTube
import Calderon.CoordinateBootstrapJets
import Calderon.ActualScalarPrincipalAdjoint
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false
noncomputable section
open Set Filter WithLp
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualNormalizedPrincipalH8InitialSmallness
open ReferenceDensityBounds CoordinateBootstrapJets PrincipalCommutator
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ConformalDepth EnergyBridge
  ActualScalarPrincipalAdjoint ExteriorAffineMetricNormalization

def parameterCanonicalCoordinatePartial (alpha : Fin 3 → Fin 9)
    (F : ℝ × R3 → ℝ) : ℝ × R3 → ℝ :=
  ((familyDirectionalDeriv 0)^[(alpha 0).val])
    (((familyDirectionalDeriv 1)^[(alpha 1).val])
      (((familyDirectionalDeriv 2)^[(alpha 2).val]) F))

theorem contDiff_parameterCanonicalCoordinatePartial
    (alpha : Fin 3 → Fin 9) (F : ℝ × R3 → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterCanonicalCoordinatePartial alpha F) := by
  have hIter (k : Fin 3) (n : ℕ) (G : ℝ × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
      ContDiff ℝ ∞ (((familyDirectionalDeriv k)^[n]) G) := by
    induction n with
    | zero => exact hG
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact contDiff_familyDirectionalDeriv k _ ih
  exact hIter 0 (alpha 0).val _
    (hIter 1 (alpha 1).val _ (hIter 2 (alpha 2).val F hF))

theorem parameterCanonicalCoordinatePartial_eq_slice
    (alpha : Fin 3 → Fin 9) (F : ℝ × R3 → ℝ) (lam : ℝ) :
    (fun x => parameterCanonicalCoordinatePartial alpha F (lam,x)) =
      canonicalCoordinatePartial alpha (fun x => F (lam,x)) := by
  have hIter (k : Fin 3) (n : ℕ) (G : ℝ × R3 → ℝ) :
      (fun x => ((familyDirectionalDeriv k)^[n] G) (lam,x)) =
        ((coordinateDerivative k)^[n]) (fun x => G (lam,x)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      funext x
      change directionalFDeriv (coordinateDirection k)
        (fun y => ((familyDirectionalDeriv k)^[n] G) (lam,y)) x =
          directionalFDeriv (coordinateDirection k)
            (((coordinateDerivative k)^[n]) (fun y => G (lam,y))) x
      rw [ih]
  dsimp only [parameterCanonicalCoordinatePartial,canonicalCoordinatePartial]
  rw [hIter 0 (alpha 0).val,hIter 1 (alpha 1).val,hIter 2 (alpha 2).val]

theorem continuous_referenceNormalizedPrincipalDifference_coordinateH8
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2) (L : ℝ) :
    Continuous (fun z : ℝ × R3 => coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L z.1) z.2) := by
  let F : Fin 3 → Fin 3 → ℝ × R3 → ℝ := fun i j z =>
    referenceNormalizedPrincipalDifference g1 g2 L z.1 z.2 i j
  have hF (i j : Fin 3) : ContDiff ℝ ∞ (F i j) :=
    contDiff_referenceNormalizedPrincipalDifference_entry_joint g1 g2 hg1 hg2 L i j
  have hEntry (alpha : Fin 3 → Fin 9) (i j : Fin 3) : Continuous
      (fun z : ℝ × R3 => canonicalCoordinatePartial alpha (fun y => F i j (z.1,y)) z.2) := by
    have he : (fun z : ℝ × R3 => canonicalCoordinatePartial alpha (fun y => F i j (z.1,y)) z.2) =
        parameterCanonicalCoordinatePartial alpha (F i j) := by
      funext z
      exact (congrFun (parameterCanonicalCoordinatePartial_eq_slice alpha (F i j) z.1) z.2).symm
    rw [he]
    exact (contDiff_parameterCanonicalCoordinatePartial alpha (F i j) (hF i j)).continuous
  have hTensor (alpha : Fin 3 → Fin 9) : Continuous (fun z : ℝ × R3 =>
      coordinateTensorPartial alpha (referenceNormalizedPrincipalDifference g1 g2 L z.1) z.2) := by
    unfold coordinateTensorPartial
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 => ℝ)).comp
      (continuous_pi (fun ij => hEntry alpha ij.1 ij.2))
  unfold coordinateH8
  exact continuous_finset_sum Finset.univ (fun alpha _ => by
    split_ifs
    · exact (hTensor alpha).norm
    · exact continuous_const)

theorem referenceNormalizedPrincipalDifference_zero_of_origin_eq_one
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (h10 : g1 0=1) (h20 : g2 0=1) (L : ℝ) (x : R3) :
    referenceNormalizedPrincipalDifference g1 g2 L 0 x=0 := by
  let c : ℝ := Real.exp (2*(-L*referenceCoordinateDepth x))
  have hc : c ≠ 0 := Real.exp_ne_zero _
  have hA : referenceMetric (dilatedMetric g1 0) L x=c • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    change Real.exp (2*(-L*referenceCoordinateDepth x)) • g1 ((0 : ℝ) • x)=c • (1 : Matrix (Fin 3) (Fin 3) ℝ)
    rw [zero_smul,h10]
  have hB : dilatedMetric g2 0 x=(1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    change g2 ((0 : ℝ) • x)=1
    rw [zero_smul,h20]
  have hDen : Matrix.trace (referenceMetric (dilatedMetric g1 0) L x*(dilatedMetric g2 0 x)⁻¹)=3*c := by
    rw [hA,hB,inv_one,Matrix.mul_one,Matrix.trace_smul,smul_eq_mul,Matrix.trace_one]
    norm_num
    <;> ring
  have hScalar : 3/(3*c)=Real.exp (2*L*referenceCoordinateDepth x) := by
    have ht : 3/(3*c)=c⁻¹ := by field_simp [hc] <;> ring
    rw [ht]
    dsimp only [c]
    rw [← Real.exp_neg]
    congr 1
    ring
  have hInv (i j : Fin 3) : ((referenceMetric (dilatedMetric g1 0) L x)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) i j =
      Real.exp (2*L*referenceCoordinateDepth x)*(1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    have ht := referenceInverseEntryFamily_eq g1 hg1 L i j (0,x)
    simpa only [referenceInverseEntryFamily,zero_smul,h10,inv_one] using ht
  unfold referenceNormalizedPrincipalDifference normalizedPrincipalDifference normalizedPrincipalMatrix
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.zero_apply]
  rw [hDen,hB,inv_one,hInv i j,hScalar]
  ring

theorem coordinateH8_referenceNormalizedPrincipalDifference_zero_of_origin_eq_one
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (h10 : g1 0=1) (h20 : g2 0=1) (L : ℝ) (x : R3) :
    coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L 0) x=0 := by
  let Z : R3 → ℝ := fun _ => 0
  have hd (k : Fin 3) : coordinateDerivative k Z=Z := by
    funext y
    simp only [coordinateDerivative,Z,directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply]
  have hi (k : Fin 3) (n : ℕ) : ((coordinateDerivative k)^[n]) Z=Z := Function.iterate_fixed (hd k) n
  have hEntry (i j : Fin 3) : (fun y => referenceNormalizedPrincipalDifference g1 g2 L 0 y i j)=Z := by
    funext y
    rw [referenceNormalizedPrincipalDifference_zero_of_origin_eq_one g1 g2 hg1 hg2 h10 h20 L y]
    rfl
  have hPartial (alpha : Fin 3 → Fin 9) (i j : Fin 3) :
      canonicalCoordinatePartial alpha (fun y => referenceNormalizedPrincipalDifference g1 g2 L 0 y i j)=Z := by
    rw [hEntry i j]
    dsimp only [canonicalCoordinatePartial]
    rw [hi 2 (alpha 2).val,hi 1 (alpha 1).val,hi 0 (alpha 0).val]
  have hTensor (alpha : Fin 3 → Fin 9) :
      coordinateTensorPartial alpha (referenceNormalizedPrincipalDifference g1 g2 L 0) x=0 := by
    apply PiLp.ext
    intro ij
    change canonicalCoordinatePartial alpha (fun y => referenceNormalizedPrincipalDifference g1 g2 L 0 y ij.1 ij.2) x=0
    rw [hPartial alpha ij.1 ij.2]
  unfold coordinateH8
  simp only [hTensor,norm_zero,ite_self,Finset.sum_const_zero]

theorem exists_referenceNormalizedPrincipalDifference_coordinateH8_small
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (h10 : g1 0=1) (h20 : g2 0=1) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) (A : ℝ) (hA : 0 < A) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ 1 ∧ ∀ lam ∈ Set.Icc (0 : ℝ) lam0,
      ∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ A := by
  let F : ℝ × R3 → ℝ := fun z => coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L z.1) z.2
  have hF : Continuous F := continuous_referenceNormalizedPrincipalDifference_coordinateH8 g1 g2 hg1 hg2 L
  have hSwap : Continuous (fun z : R3 × ℝ => F (z.2,z.1)) :=
    hF.comp continuous_swap
  have hZero : ∀ x ∈ K, F (0,x)=0 := by
    intro x _
    exact coordinateH8_referenceNormalizedPrincipalDifference_zero_of_origin_eq_one
      g1 g2 hg1 hg2 h10 h20 L x
  obtain ⟨lam0,hlam0,hlam01,hSmall⟩ :=
    ConnectionError.exists_signed_radius_of_compact_zero_slice
      (fun z : R3 × ℝ => F (z.2,z.1)) hSwap K hK 1 zero_lt_one A hA hZero
  refine ⟨lam0,hlam0,hlam01,?_⟩
  intro lam hlam x hx
  have hAbs : |lam| ≤ lam0 := by
    rw [abs_of_nonneg hlam.1]
    exact hlam.2
  have hBound : ‖F (lam,x)‖ < A := hSmall x hx lam hAbs
  exact (le_abs_self (F (lam,x))).trans (by
    simpa only [Real.norm_eq_abs] using hBound.le)

/-- Genuine initial delta=1 smallness for the explicitly normalized frozen exterior pair.
The fixed profile p,R precedes lam0. All-delta propagation and energy/chart transport are separate. -/
theorem exists_exteriorAffineNormalized_coordinateH8_initial_profile
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (e : R3) (he : ‖e‖=1) (L R : ℝ) (p : ℕ) (hR : 0 < R)
    (K : Set R3) (hK : IsCompact K) (eps : ℝ) (heps : 0 < eps) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ 1 ∧ ∀ lam ∈ Set.Icc (0 : ℝ) lam0,
      ∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference
        (exteriorAffineNormalizedMetric g1 e) (exteriorAffineNormalizedMetric g2 e) L lam) x ≤
        eps*referenceRadius 1 R p L x := by
  let g1n : MatrixField := exteriorAffineNormalizedMetric g1 e
  let g2n : MatrixField := exteriorAffineNormalizedMetric g2 e
  have h1n : IsAdmissibleMetric g1n := isAdmissibleMetric_exteriorAffineNormalizedMetric g1 hg1 e he
  have h2n : IsAdmissibleMetric g2n := isAdmissibleMetric_exteriorAffineNormalizedMetric g2 hg2 e he
  have h10 : g1n 0=1 := exteriorAffineNormalizedMetric_zero_eq_one g1 hg1 e he
  have h20 : g2n 0=1 := exteriorAffineNormalizedMetric_zero_eq_one g2 hg2 e he
  have hr : Continuous (referenceRadius 1 R p L) :=
    (contDiff_referenceRadius_actual 1 R p L (by norm_num) hR).continuous
  obtain ⟨m,hm,hLower⟩ := hK.exists_forall_le' hr.continuousOn
    (a := (0 : ℝ)) (fun x _ => referenceRadius_pos 1 R p L x (by norm_num) hR)
  obtain ⟨lam0,hlam0,hlam01,hSmall⟩ :=
    exists_referenceNormalizedPrincipalDifference_coordinateH8_small g1n g2n h1n h2n h10 h20 L K hK
      (eps*m) (mul_pos heps hm)
  refine ⟨lam0,hlam0,hlam01,?_⟩
  intro lam hlam x hx
  exact (hSmall lam hlam x hx).trans (mul_le_mul_of_nonneg_left (hLower x hx) heps.le)

end OAI.AnisotropicCalderon.ActualNormalizedPrincipalH8InitialSmallness
