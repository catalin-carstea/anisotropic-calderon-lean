import Calderon.PerturbedDensityAdjoint
import Calderon.ProfileRadiusJets

noncomputable section
open Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds PerturbedDensityAdjoint
open ConformalDepth

lemma norm_coordinateDirection (i : Fin 3) : ‖coordinateDirection i‖ = 1 := by
  simp [coordinateDirection]

lemma abs_coordinate_first_le (i : Fin 3) (f : R3 → ℝ) (x : R3) :
    |directionalFDeriv (coordinateDirection i) f x| ≤ ‖iteratedFDeriv ℝ 1 f x‖ := by
  simpa [directionalFDeriv, norm_coordinateDirection, norm_iteratedFDeriv_one]
    using (fderiv ℝ f x).le_opNorm (coordinateDirection i)

lemma abs_coordinate_second_le (i j : Fin 3) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : R3) :
    |directionalFDeriv (coordinateDirection j)
      (directionalFDeriv (coordinateDirection i) f) x| ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
  have hD := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  unfold directionalFDeriv
  rw [fderiv_clm_apply (hD x) (differentiableAt_const (coordinateDirection i))]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const_apply, zero_apply, map_zero, zero_add]
  have hn := ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ f) x)
    (coordinateDirection j) (coordinateDirection i)
  have he : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]
  simpa only [Real.norm_eq_abs, norm_coordinateDirection, mul_one, he] using hn

lemma contDiff_referenceRadius_actual (δ R : ℝ) (p : ℕ) (L : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) : ContDiff ℝ ∞ (referenceRadius δ R p L) := by
  have he : (fun y => Real.exp (Real.log (referenceRadius δ R p L y))) =
      referenceRadius δ R p L := by
    funext y
    exact Real.exp_log (referenceRadius_pos δ R p L y hδ hR)
  rw [← he]
  exact (contDiff_log_referenceRadius_profile δ R L p hδ hR).exp

def actualPrincipalMatrix (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (x : R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => referenceRadius δ R p L x *
    (referenceInverseEntryFamily g L i j (lam,x) + h x i j)

lemma actualPrincipalMatrix_entry (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (i j : Fin 3) :
    (fun x => actualPrincipalMatrix g L lam δ R p h x i j) =
      principalEntry (referenceRadius δ R p L)
        (fun x => referenceInverseEntryFamily g L i j (lam,x)) (fun x => h x i j) := rfl

/-- All constants are selected from the actual fixed background before shrink parameters or h. -/
theorem exists_actual_weighted_principal_uniform_bounds (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ M C1 C2 : ℝ, 1 ≤ M ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps →
      |(referenceDensityFamily g L (lam,x))⁻¹| ≤ M ∧
      ∀ i j k l,
        |directionalFDeriv (coordinateDirection k)
          (fun y => referenceDensityFamily g L (lam,y) *
            actualPrincipalMatrix g L lam δ R p h y i j) x| ≤ C1 * eps / beta ∧
        |directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k)
          (fun y => referenceDensityFamily g L (lam,y) *
            actualPrincipalMatrix g L lam δ R p h y i j)) x| ≤ C2 * eps := by
  obtain ⟨M,hM,hbackground⟩ := exists_referenceBackground_uniform_two_jet_bound g hg L K hK
  obtain ⟨J1,hJ1,hjet1⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 1
  obtain ⟨J2,hJ2,hjet2⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 2
  refine ⟨M,(J1+2)*M*(M+1),(J2+4*J1+4)*M*(M+1),hM,by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall
  have hmi := hbackground lam hlam x hx (.inl 1) (.inl ())
  refine ⟨by simpa [coordinateJetFamily,referenceBackgroundFamily] using hmi,?_⟩
  intro i j k l
  let mu : R3 → ℝ := fun y => referenceDensityFamily g L (lam,y)
  let q : R3 → ℝ := fun y => referenceInverseEntryFamily g L i j (lam,y)
  have hslice : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp hslice
  have hq : ContDiff ℝ ∞ q := (contDiff_referenceInverseEntryFamily g hg L i j).comp hslice
  have hmu : TwoJetBound (coordinateDirection k) (coordinateDirection l) mu x M := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa [coordinateJetFamily,referenceBackgroundFamily,mu] using
        hbackground lam hlam x hx (.inl 0) (.inl ())
    · simpa [coordinateJetFamily,referenceBackgroundFamily,familyDirectionalDeriv,mu] using
        hbackground lam hlam x hx (.inl 0) (.inr (.inl k))
    · simpa [coordinateJetFamily,referenceBackgroundFamily,familyDirectionalDeriv,mu] using
        hbackground lam hlam x hx (.inl 0) (.inr (.inl l))
    · simpa [coordinateJetFamily,referenceBackgroundFamily,familyDirectionalDeriv,mu] using
        hbackground lam hlam x hx (.inl 0) (.inr (.inr (k,l)))
  have hqq : TwoJetBound (coordinateDirection k) (coordinateDirection l) q x M := by
    refine ⟨?_,?_,?_,?_⟩
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inl ())
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inr (.inl k))
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inr (.inl l))
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inr (.inr (k,l)))
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have h1 := (hjet1 lam hlam δ hδ hδ1 R hR p hp x hx).1
  have h2 := (hjet2 lam hlam δ hδ hδ1 R hR p hp x hx).1
  have h1k := (abs_coordinate_first_le k (referenceRadius δ R p L) x).trans h1
  have h1l := (abs_coordinate_first_le l (referenceRadius δ R p L) x).trans h1
  have h2kl := (abs_coordinate_second_le k l (referenceRadius δ R p L) hr x).trans h2
  have ht := density_principal_first_second_bounds (coordinateDirection k) (coordinateDirection l)
    mu (referenceRadius δ R p L) q (fun y => h y i j) hm hr hq (hh i j) x
    M J1 J2 beta eps hM hJ1.le hJ2.le hb heps heps1
    (referenceRadius_pos δ R p L x hδ hR) hsmall hmu hqq (hhjet i j k l)
    (by simpa only [pow_one] using h1k) (by simpa only [pow_one] using h1l) h2kl
  exact ht

-- These definitions are the actual coefficient functions in the checked scalar formal adjoint.
def adjointFirstCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (x : R3) (i : Fin 3) : ℝ :=
  2 * (mu x)⁻¹ * ∑ j, directionalFDeriv (v j) (fun y => mu y * a y i j) x

def adjointZeroCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (x : R3) : ℝ :=
  (mu x)⁻¹ * ∑ i, ∑ j, directionalFDeriv (v j)
    (directionalFDeriv (v i) (fun y => mu y * a y i j)) x

lemma abs_sum_three_le (f : Fin 3 → ℝ) (B : ℝ) (h : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 3*B := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B := Finset.sum_le_sum (fun i _ => h i)
    _ = 3*B := by simp

lemma adjointFirstCoefficient_bound (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (x : R3) (M B : ℝ) (hM : 0 ≤ M)
    (hm : |(mu x)⁻¹| ≤ M)
    (h : ∀ i j, |directionalFDeriv (v j) (fun y => mu y*a y i j) x| ≤ B)
    (i : Fin 3) : |adjointFirstCoefficient v mu a x i| ≤ 6*M*B := by
  have hs := abs_sum_three_le _ B (h i)
  unfold adjointFirstCoefficient
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have ht := mul_le_mul hm hs (abs_nonneg _) hM
  nlinarith

lemma adjointZeroCoefficient_bound (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (x : R3) (M B : ℝ) (hM : 0 ≤ M)
    (hm : |(mu x)⁻¹| ≤ M)
    (h : ∀ i j, |directionalFDeriv (v j) (directionalFDeriv (v i)
      (fun y => mu y*a y i j)) x| ≤ B) :
    |adjointZeroCoefficient v mu a x| ≤ 9*M*B := by
  have hs := abs_sum_three_le _ (3*B) (fun i => abs_sum_three_le _ B (h i))
  unfold adjointZeroCoefficient
  rw [abs_mul]
  have ht := mul_le_mul hm hs (abs_nonneg _) hM
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalarSecondBaseAdjoint_coefficient_form (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (w : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hw : ContDiff ℝ ∞ w)
    (x : R3) (hp : mu x ≠ 0) (hs : ∀ᶠ y in 𝓝 x, (a y).IsHermitian) :
    scalarSecondBaseAdjoint v mu a w x - scalarSecondBase v a w x =
      adjointZeroCoefficient v mu a x • w x +
      ∑ i, adjointFirstCoefficient v mu a x i • directionalFDeriv (v i) w x := by
  rw [scalarSecondBaseAdjoint_sub v mu a w hm ha hw x hp hs]
  simp only [adjointZeroCoefficient,adjointFirstCoefficient,Finset.mul_sum,Finset.sum_smul,
    Finset.smul_sum,smul_smul]

end OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint
