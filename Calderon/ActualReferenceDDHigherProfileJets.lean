import Calderon.ActualReferenceDDHigherGeometryJets
import Calderon.ProfileRadiusJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualReferenceDDHigherProfileJets
open ActualReferenceDDHigherGeometryJets ActualScalarPrincipalAdjoint
  PrincipalCommutator ReferenceDensityBounds ConformalDepth RadiusProfile MetricOperator

lemma norm_iteratedFDeriv_coordinateFieldWordPartial_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (f : R3 → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : R3) :
    ‖iteratedFDeriv ℝ n (coordinateFieldWordPartial w f) x‖ ≤
      ‖iteratedFDeriv ℝ (n+w.length) f x‖ := by
  induction w generalizing n with
  | nil => simp only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,le_refl]
  | cons k w ih =>
    have hW := contDiff_coordinateFieldWordPartial w f hf
    have ht : ‖iteratedFDeriv ℝ n
        (directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w f)) x‖ ≤
        ‖iteratedFDeriv ℝ (n+1) (coordinateFieldWordPartial w f) x‖ := by
      change ‖iteratedFDeriv ℝ n
          (fun y => fderiv ℝ (coordinateFieldWordPartial w f) y (coordinateDirection k)) x‖ ≤
        ‖iteratedFDeriv ℝ (n+1) (coordinateFieldWordPartial w f) x‖
      simpa only [norm_coordinateDirection,one_mul,norm_iteratedFDeriv_fderiv] using
        (norm_iteratedFDeriv_clm_apply_const
          (c := coordinateDirection k)
          (n := n) (x := x)
          ((hW.fderiv_right (m := ∞) (by simp)).contDiffAt) (by simp))
    have hu := ht.trans (ih (n+1))
    have horder : n+1+w.length = n+(w.length+1) := by omega
    rw [horder] at hu
    simpa only [coordinateFieldWordPartial,List.length_cons] using hu

lemma norm_coordinateFieldWordPartial_le_iteratedFDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (f : R3 → E) (hf : ContDiff ℝ ∞ f) (x : R3) :
    ‖coordinateFieldWordPartial w f x‖ ≤ ‖iteratedFDeriv ℝ w.length f x‖ := by
  have ht := norm_iteratedFDeriv_coordinateFieldWordPartial_le w f hf 0 x
  rw [show 0+w.length = w.length by omega] at ht
  simpa only [norm_iteratedFDeriv_zero] using ht

theorem exists_referenceRadius_uniform_coordinate_word_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ w : List (Fin 3), w.length ≤ N →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      |coordinateFieldWordPartial w (referenceRadius δ R p L) x| ≤
        C*referenceRadius δ R p L x*beta^w.length ∧
      |coordinateFieldWordPartial w (fun y => (referenceRadius δ R p L y)⁻¹) x| ≤
        C*(referenceRadius δ R p L x)⁻¹*beta^w.length := by
  classical
  have hfamily : ∀ i : Fin (N+1), ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i.val (referenceRadius δ R p L) x‖ ≤
        C*referenceRadius δ R p L x*
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x^i.val ∧
      ‖iteratedFDeriv ℝ i.val (fun y => (referenceRadius δ R p L y)⁻¹) x‖ ≤
        C*(referenceRadius δ R p L x)⁻¹*
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x^i.val := by
    intro i
    exact exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds g hg L hL K hK i.val
  choose Cs hCs hbounds using hfamily
  let C : ℝ := 1+∑ i : Fin (N+1), |Cs i|
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ i : Fin (N+1), |Cs i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp [C]
    linarith
  have hCi (i : Fin (N+1)) : Cs i ≤ C := by
    have ht := (le_abs_self (Cs i)).trans
      (Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin (N+1) => |Cs j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx w hw beta
  let i : Fin (N+1) := ⟨w.length,by omega⟩
  have hr := referenceRadius_pos δ R p L x hδ hR
  have hb : 0 ≤ beta := Real.sqrt_nonneg _
  have hbp : 0 ≤ beta^w.length := pow_nonneg hb _
  have hjet := hbounds i lam hlam δ hδ hδ1 R hR p hp x hx
  have hs := contDiff_referenceRadius_actual δ R p L hδ hR
  have hsinv : ContDiff ℝ ∞ (fun y => (referenceRadius δ R p L y)⁻¹) :=
    hs.inv (fun y => (referenceRadius_pos δ R p L y hδ hR).ne')
  refine ⟨?_,?_⟩
  · have hword : |coordinateFieldWordPartial w (referenceRadius δ R p L) x| ≤
        ‖iteratedFDeriv ℝ w.length (referenceRadius δ R p L) x‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_coordinateFieldWordPartial_le_iteratedFDeriv w _ hs x
    have hscalar := mul_le_mul_of_nonneg_right (hCi i) hr.le
    exact hword.trans (hjet.1.trans (mul_le_mul_of_nonneg_right hscalar hbp))
  · have hword : |coordinateFieldWordPartial w (fun y => (referenceRadius δ R p L y)⁻¹) x| ≤
        ‖iteratedFDeriv ℝ w.length (fun y => (referenceRadius δ R p L y)⁻¹) x‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_coordinateFieldWordPartial_le_iteratedFDeriv w _ hsinv x
    have hscalar := mul_le_mul_of_nonneg_right (hCi i) (inv_nonneg.mpr hr.le)
    exact hword.trans (hjet.2.trans (mul_le_mul_of_nonneg_right hscalar hbp))

theorem exists_log_referenceRadius_uniform_positive_coordinate_word_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ w : List (Fin 3), 1 ≤ w.length → w.length ≤ N →
      |coordinateFieldWordPartial w (fun y => Real.log (referenceRadius δ R p L y)) x| ≤
        C*metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
          (fun y => Real.log (referenceRadius δ R p L y)) x^w.length := by
  classical
  obtain ⟨J,hJ,hjet⟩ := exists_dilated_referenceRadius_fixed_uniform_jet_envelope g hg L hL K hK N
  let C : ℝ := 1+∑ i : Fin (N+1), J^i.val
  have hJ0 : 0 ≤ J := by linarith
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ i : Fin (N+1), J^i.val := Finset.sum_nonneg (fun i _ => pow_nonneg hJ0 _)
    dsimp [C]
    linarith
  have hCi (i : Fin (N+1)) : J^i.val ≤ C := by
    have ht := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin (N+1) => J^j.val)
      (fun j _ => pow_nonneg hJ0 _) (Finset.mem_univ i)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx w hw1 hwN
  let i : Fin (N+1) := ⟨w.length,by omega⟩
  let beta : ℝ := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
    (fun y => Real.log (referenceRadius δ R p L y)) x
  have hb : 0 ≤ beta := Real.sqrt_nonneg _
  have hword : |coordinateFieldWordPartial w (fun y => Real.log (referenceRadius δ R p L y)) x| ≤
      ‖iteratedFDeriv ℝ w.length (fun y => Real.log (referenceRadius δ R p L y)) x‖ := by
    simpa only [Real.norm_eq_abs] using norm_coordinateFieldWordPartial_le_iteratedFDeriv w _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR) x
  have ht := hjet lam hlam δ hδ hδ1 R hR p hp x hx w.length hw1 hwN
  have hm := mul_le_mul_of_nonneg_right (hCi i) (pow_nonneg hb w.length)
  exact hword.trans (ht.trans (by simpa only [mul_pow] using hm))

end OAI.AnisotropicCalderon.ActualReferenceDDHigherProfileJets
