import Calderon.DilatedDepthUniform
import Calderon.PrincipalDirectional

noncomputable section
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ReferenceDensityBounds
open ConformalDepth EnergyBridge PrincipalCommutator

def coordinateDirection (i : Fin 3) : R3 := EuclideanSpace.single i 1

def familyDirectionalDeriv (i : Fin 3) (F : ℝ × R3 → ℝ) (z : ℝ × R3) : ℝ :=
  directionalFDeriv (coordinateDirection i) (fun y => F (z.1, y)) z.2

lemma familyDirectionalDeriv_eq (i : Fin 3) (F : ℝ × R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) (z : ℝ × R3) :
    familyDirectionalDeriv i F z = fderiv ℝ F z (0, coordinateDirection i) := by
  have hp : HasFDerivAt (fun y : R3 => (z.1,y))
      (ContinuousLinearMap.inr ℝ ℝ R3) z.2 := hasFDerivAt_prodMk_right z.1 z.2
  have h := ((hF.differentiable (by simp) z).hasFDerivAt).comp z.2 hp
  unfold familyDirectionalDeriv directionalFDeriv
  change (fderiv ℝ (F ∘ fun y : R3 => (z.1,y)) z.2) (coordinateDirection i) = _
  rw [h.fderiv]
  rfl

lemma contDiff_familyDirectionalDeriv (i : Fin 3) (F : ℝ × R3 → ℝ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (familyDirectionalDeriv i F) := by
  have he : familyDirectionalDeriv i F =
      fun z => fderiv ℝ F z (0, coordinateDirection i) :=
    funext (familyDirectionalDeriv_eq i F hF)
  rw [he]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

def referenceDensityFamily (g : MatrixField) (L : ℝ) (z : ℝ × R3) : ℝ :=
  vol (referenceMetric (dilatedMetric g z.1) L) z.2

lemma referenceDensityFamily_eq (g : MatrixField) (L : ℝ) (z : ℝ × R3) :
    referenceDensityFamily g L z = Real.exp (-3 * L * referenceCoordinateDepth z.2) *
      vol g (z.1 • z.2) := by
  unfold referenceDensityFamily referenceMetric
  rw [vol_conformalMatrix]
  congr 1
  ring

lemma contDiff_referenceDensityFamily (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) : ContDiff ℝ ∞ (referenceDensityFamily g L) := by
  have he : referenceDensityFamily g L = fun z =>
      Real.exp (-3 * L * referenceCoordinateDepth z.2) * vol g (z.1 • z.2) :=
    funext (referenceDensityFamily_eq g L)
  rw [he]
  exact ((contDiff_const.mul (contDiff_referenceCoordinateDepth.comp contDiff_snd)).exp).mul
    ((contDiff_vol g hg).comp (contDiff_fst.smul contDiff_snd))

lemma referenceDensityFamily_pos (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (z : ℝ × R3) : 0 < referenceDensityFamily g L z := by
  exact vol_pos_of_posDef _
    (conformalMatrix_posDef _ _ (dilatedMetric_posDef g hg z.1)) z.2

lemma contDiff_referenceDensityFamily_inv (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) : ContDiff ℝ ∞ (fun z => (referenceDensityFamily g L z)⁻¹) :=
  (contDiff_referenceDensityFamily g hg L).inv
    (fun z => ne_of_gt (referenceDensityFamily_pos g hg L z))

def referenceInverseEntryFamily (g : MatrixField) (L : ℝ) (i j : Fin 3)
    (z : ℝ × R3) : ℝ :=
  ((referenceMetric (dilatedMetric g z.1) L z.2)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) i j

lemma referenceInverseEntryFamily_eq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i j : Fin 3) (z : ℝ × R3) :
    referenceInverseEntryFamily g L i j z =
      Real.exp (2 * L * referenceCoordinateDepth z.2) * (g (z.1 • z.2))⁻¹ i j := by
  unfold referenceInverseEntryFamily referenceMetric
  rw [conformalMatrix_inverse _ _ (dilatedMetric_posDef g hg z.1)]
  simp only [Matrix.smul_apply, smul_eq_mul]
  congr 2
  ring

lemma contDiff_referenceInverseEntryFamily (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i j : Fin 3) : ContDiff ℝ ∞ (referenceInverseEntryFamily g L i j) := by
  have he : referenceInverseEntryFamily g L i j = fun z =>
      Real.exp (2 * L * referenceCoordinateDepth z.2) * (g (z.1 • z.2))⁻¹ i j :=
    funext (referenceInverseEntryFamily_eq g hg L i j)
  rw [he]
  exact ((contDiff_const.mul (contDiff_referenceCoordinateDepth.comp contDiff_snd)).exp).mul
    ((contDiff_metric_inverse_entry g hg i j).comp (contDiff_fst.smul contDiff_snd))

abbrev JetTag := Sum Unit (Sum (Fin 3) (Fin 3 × Fin 3))

def coordinateJetFamily (F : ℝ × R3 → ℝ) : JetTag → ℝ × R3 → ℝ
  | .inl _ => F
  | .inr (.inl i) => familyDirectionalDeriv i F
  | .inr (.inr (i,j)) => familyDirectionalDeriv j (familyDirectionalDeriv i F)

lemma continuous_coordinateJetFamily (F : ℝ × R3 → ℝ) (hF : ContDiff ℝ ∞ F)
    (t : JetTag) : Continuous (coordinateJetFamily F t) := by
  rcases t with t | (i | ⟨i,j⟩)
  · exact hF.continuous
  · exact (contDiff_familyDirectionalDeriv i F hF).continuous
  · exact (contDiff_familyDirectionalDeriv j _ (contDiff_familyDirectionalDeriv i F hF)).continuous

theorem exists_uniform_bound_finite_family {ι : Type*} [Fintype ι]
    (F : ι → ℝ × R3 → ℝ) (hF : ∀ i, Continuous (F i))
    (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ x ∈ K, ∀ i, |F i (lam,x)| ≤ M := by
  classical
  have he : ∀ i, ∃ B : ℝ, ∀ z ∈ (Set.Icc (0 : ℝ) 1) ×ˢ K, |F i z| ≤ B :=
    fun i => (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hF i).continuousOn
  choose B hB using he
  let M := max 1 (∑ i, |B i|)
  refine ⟨M, le_max_left _ _, ?_⟩
  intro lam hlam x hx i
  exact (hB i (lam,x) ⟨hlam,hx⟩).trans ((le_abs_self _).trans
    ((Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_univ i)).trans
      (le_max_right _ _)))

abbrev BackgroundTag := Sum (Fin 2) (Fin 3 × Fin 3)

def referenceBackgroundFamily (g : MatrixField) (L : ℝ) : BackgroundTag → ℝ × R3 → ℝ
  | .inl k => if k = 0 then referenceDensityFamily g L
      else fun z => (referenceDensityFamily g L z)⁻¹
  | .inr (i,j) => referenceInverseEntryFamily g L i j

lemma contDiff_referenceBackgroundFamily (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (t : BackgroundTag) : ContDiff ℝ ∞ (referenceBackgroundFamily g L t) := by
  rcases t with k | ⟨i,j⟩
  · by_cases hk : k = 0
    · simpa [referenceBackgroundFamily,hk] using contDiff_referenceDensityFamily g hg L
    · simpa [referenceBackgroundFamily,hk] using contDiff_referenceDensityFamily_inv g hg L
  · exact contDiff_referenceInverseEntryFamily g hg L i j

/-- One actual fixed compact bound for rho, rho inverse and Qgamma through two base derivatives. -/
theorem exists_referenceBackground_uniform_two_jet_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ x ∈ K, ∀ t : BackgroundTag, ∀ s : JetTag,
        |coordinateJetFamily (referenceBackgroundFamily g L t) s (lam,x)| ≤ M := by
  obtain ⟨M,hM,hbound⟩ := exists_uniform_bound_finite_family
    (fun t : BackgroundTag × JetTag => coordinateJetFamily (referenceBackgroundFamily g L t.1) t.2)
    (fun t => continuous_coordinateJetFamily _ (contDiff_referenceBackgroundFamily g hg L t.1) t.2)
    K hK
  exact ⟨M,hM,fun lam hlam x hx t s => hbound lam hlam x hx (t,s)⟩

end OAI.AnisotropicCalderon.ReferenceDensityBounds
