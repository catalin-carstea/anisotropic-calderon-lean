import Calderon.CollaboratorWkpCalculusOct17
import TauCeti.Analysis.Sobolev.W1p.Translation
import TauCeti.Analysis.Sobolev.W1p.CompactSupport

/-! Affine changes of variables `y ↦ c + ρ y` between `ball c ρ` and the unit ball, acting on
`W^{k,2}` and `H¹₀` (helper for tasks 07–09). -/

noncomputable section
open MeasureTheory TopologicalSpace Metric
namespace OAI.AnisotropicCalderon.Affine
open TauCeti EnergyBridge

/-- `ball c ρ` as an open set. -/
def ballO (c : R3) (ρ : ℝ) : Opens R3 := ⟨ball c ρ, isOpen_ball⟩

/-- The affine map `x ↦ c + ρ • x`. -/
def aff (c : R3) (ρ : ℝ) (x : R3) : R3 := c + ρ • x

theorem aff_apply (c : R3) (ρ : ℝ) (x : R3) : aff c ρ x = c + ρ • x := rfl

/-- The affine map as a homeomorphism. -/
def affH (c : R3) {ρ : ℝ} (hρ : ρ ≠ 0) : R3 ≃ₜ R3 :=
  (Homeomorph.smulOfNeZero ρ hρ).trans (Homeomorph.addLeft c)

theorem coe_affH (c : R3) {ρ : ℝ} (hρ : ρ ≠ 0) : ⇑(affH c hρ) = aff c ρ := rfl

theorem measurable_aff (c : R3) (ρ : ℝ) : Measurable (aff c ρ) :=
  (measurable_const_add c).comp (measurable_const_smul ρ)

theorem continuous_aff (c : R3) (ρ : ℝ) : Continuous (aff c ρ) := by
  unfold aff; fun_prop

theorem measurePreserving_aff (c : R3) {ρ : ℝ} (hρ : 0 < ρ) :
    MeasurePreserving (aff c ρ) (ENNReal.ofReal (ρ ^ 3) • (volume : Measure R3)) volume := by
  refine ⟨measurable_aff c ρ, ?_⟩
  have : aff c ρ = (c + ·) ∘ (ρ • ·) := rfl
  rw [this, ← Measure.map_map (measurable_const_add c) (measurable_const_smul ρ),
    Measure.map_smul, Measure.map_addHaar_smul _ hρ.ne', smul_smul, finrank_euclideanSpace,
    Fintype.card_fin, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
    mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_smul]
  · exact map_add_left_eq_self volume c
  · exact (measurable_const_smul ρ).aemeasurable

/-- The domain condition: `aff c ρ` maps `V` onto `Ω`. -/
def IsAff (Ω V : Opens R3) (c : R3) (ρ : ℝ) : Prop :=
  ∀ x, c + ρ • x ∈ (Ω : Set R3) ↔ x ∈ (V : Set R3)

variable {Ω V : Opens R3} {c : R3} {ρ : ℝ}

theorem preimage_aff (h : IsAff Ω V c ρ) : aff c ρ ⁻¹' (Ω : Set R3) = V := by
  ext x; exact h x

/-- The constant `s = ρ³`. -/
@[inline, reducible] def sc (ρ : ℝ) : ENNReal := ENNReal.ofReal (ρ ^ 3)

theorem sc_ne_zero (hρ : 0 < ρ) : sc ρ ≠ 0 := by
  simp only [sc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity

theorem sc_ne_top : sc ρ ≠ ⊤ := ENNReal.ofReal_ne_top

theorem mp_restrict (hρ : 0 < ρ) (h : IsAff Ω V c ρ) :
    MeasurePreserving (aff c ρ) (sc ρ • (volume : Measure R3).restrict V)
      ((volume : Measure R3).restrict Ω) := by
  have := (measurePreserving_aff c hρ).restrict_preimage Ω.isOpen.measurableSet
  rwa [preimage_aff h, Measure.restrict_smul] at this

theorem qmp (hρ : 0 < ρ) (h : IsAff Ω V c ρ) :
    Measure.QuasiMeasurePreserving (aff c ρ) ((volume : Measure R3).restrict V)
      ((volume : Measure R3).restrict Ω) :=
  (mp_restrict hρ h).quasiMeasurePreserving.mono_left
    (Measure.absolutelyContinuous_smul (sc_ne_zero hρ))

theorem restrict_eq_inv_smul (hρ : 0 < ρ) :
    (volume : Measure R3).restrict V = (sc ρ)⁻¹ • (sc ρ • (volume : Measure R3).restrict V) := by
  rw [smul_smul, ENNReal.inv_mul_cancel (sc_ne_zero hρ) sc_ne_top, one_smul]

section Lp
variable {F : Type*} [NormedAddCommGroup F]

theorem memLp_comp (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (f : Lp F 2 ((volume : Measure R3).restrict Ω)) :
    MemLp (fun x => f (c + ρ • x)) 2 ((volume : Measure R3).restrict V) := by
  have h1 := (Lp.memLp f).comp_measurePreserving (mp_restrict hρ h)
  rw [restrict_eq_inv_smul (V := V) hρ]
  exact h1.smul_measure (ENNReal.inv_ne_top.2 (sc_ne_zero hρ))

theorem eLpNorm_comp (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (f : Lp F 2 ((volume : Measure R3).restrict Ω)) :
    eLpNorm (fun x => f (c + ρ • x)) 2 ((volume : Measure R3).restrict V) =
      (sc ρ)⁻¹ ^ (1 / (2 : ENNReal)).toReal • eLpNorm f 2 ((volume : Measure R3).restrict Ω) := by
  have h1 : MemLp (fun x => f (c + ρ • x)) 2 (sc ρ • (volume : Measure R3).restrict V) :=
    (Lp.memLp f).comp_measurePreserving (mp_restrict hρ h)
  rw [restrict_eq_inv_smul (V := V) hρ, eLpNorm_smul_measure_of_ne_top (by simp) _ _ h1.aestronglyMeasurable]
  congr 1
  exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) (mp_restrict hρ h)

variable [NormedSpace ℝ F]

/-- The constant in the norm identity. -/
def kC (ρ : ℝ) : ℝ := ((sc ρ)⁻¹ ^ (1 / (2 : ENNReal)).toReal).toReal

/-- Composition with the affine map on `L²`, as a linear map. -/
def compLm (hρ : 0 < ρ) (h : IsAff Ω V c ρ) :
    Lp F 2 ((volume : Measure R3).restrict Ω) →ₗ[ℝ] Lp F 2 ((volume : Measure R3).restrict V) where
  toFun f := (memLp_comp hρ h f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_comp hρ h (f + g)).coeFn_toLp, (memLp_comp hρ h f).coeFn_toLp,
      (memLp_comp hρ h g).coeFn_toLp,
      Lp.coeFn_add ((memLp_comp hρ h f).toLp _) ((memLp_comp hρ h g).toLp _),
      (qmp hρ h).ae (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h4, Pi.add_apply, h1, h2, h3]
    exact h5
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [(memLp_comp hρ h (a • f)).coeFn_toLp, (memLp_comp hρ h f).coeFn_toLp,
      Lp.coeFn_smul a ((memLp_comp hρ h f).toLp _),
      (qmp hρ h).ae (Lp.coeFn_smul a f)] with x h1 h2 h4 h5
    simp only [RingHom.id_apply]
    rw [h4, Pi.smul_apply, h1, h2]
    exact h5

theorem norm_compLm (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (f : Lp F 2 ((volume : Measure R3).restrict Ω)) :
    ‖compLm hρ h f‖ = kC ρ * ‖f‖ := by
  change ‖(memLp_comp hρ h f).toLp _‖ = _
  rw [Lp.norm_toLp, eLpNorm_comp hρ h, Lp.norm_def, kC, smul_eq_mul, ENNReal.toReal_mul]

/-- Composition with the affine map on `L²`. -/
def compL (hρ : 0 < ρ) (h : IsAff Ω V c ρ) :
    Lp F 2 ((volume : Measure R3).restrict Ω) →L[ℝ] Lp F 2 ((volume : Measure R3).restrict V) :=
  (compLm hρ h).mkContinuous (kC ρ) fun f => (norm_compLm hρ h f).le

theorem compL_ae (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (f : Lp F 2 ((volume : Measure R3).restrict Ω)) :
    ⇑(compL hρ h f) =ᵐ[(volume : Measure R3).restrict V] fun x => f (c + ρ • x) :=
  (memLp_comp hρ h f).coeFn_toLp

end Lp

/-! ### Change of variables and test functions -/

theorem measurableEmbedding_aff (c : R3) {ρ : ℝ} (hρ : 0 < ρ) : MeasurableEmbedding (aff c ρ) :=
  (affH c hρ.ne').measurableEmbedding

theorem integral_comp_aff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : R3)
    (hρ : 0 < ρ) (g : R3 → F) :
    ∫ x, g (c + ρ • x) = (sc ρ).toReal⁻¹ • ∫ y, g y := by
  have h1 := (measurePreserving_aff c hρ).integral_comp (measurableEmbedding_aff c hρ) g
  rw [integral_smul_measure] at h1
  have hs : (sc ρ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨sc_ne_zero hρ, sc_ne_top⟩
  rw [← h1, smul_smul, inv_mul_cancel₀ hs, one_smul]
  rfl

theorem isAff_symm (hρ : 0 < ρ) (h : IsAff Ω V c ρ) : IsAff V Ω (-(ρ⁻¹ • c)) ρ⁻¹ := by
  intro x
  have hx : c + ρ • (-(ρ⁻¹ • c) + ρ⁻¹ • x) = x := by
    rw [smul_add, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, one_smul]
    abel
  rw [← h, hx]

theorem aff_symm_aff (hρ : 0 < ρ) (x w : R3) :
    -(ρ⁻¹ • c) + ρ⁻¹ • (c + ρ • x + w) = x + ρ⁻¹ • w := by
  rw [smul_add, smul_add, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
  abel

theorem aff_aff_symm (hρ : 0 < ρ) (x : R3) :
    c + ρ • (-(ρ⁻¹ • c) + ρ⁻¹ • x) = x := by
  rw [smul_add, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, one_smul]
  abel

open scoped Distributions InnerProductSpace

/-- Compose a test function on `Ω` with the affine map, giving a test function on `V`. -/
def compTest (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (φ : 𝓓(Ω, ℝ)) : 𝓓(V, ℝ) :=
  ⟨fun x => φ (c + ρ • x), φ.contDiff.comp (by fun_prop),
    φ.hasCompactSupport.comp_homeomorph (affH c hρ.ne'),
    by
      intro x hx
      have : x ∈ tsupport ((φ : R3 → ℝ) ∘ (affH c hρ.ne' : R3 → R3)) := hx
      rw [tsupport_comp_eq_preimage] at this
      exact (h x).1 (φ.tsupport_subset this)⟩

@[simp]
theorem compTest_apply (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (φ : 𝓓(Ω, ℝ)) (x : R3) :
    compTest hρ h φ x = φ (c + ρ • x) := rfl

theorem integrableOn_comp (hρ : 0 < ρ) {F : Type*} [NormedAddCommGroup F] {f : R3 → F}
    {K : Set R3} (hf : IntegrableOn f (aff c ρ '' K) volume) :
    IntegrableOn (fun x => f (c + ρ • x)) K volume := by
  have h2 := (measurePreserving_aff c hρ).integrableOn_comp_preimage
    (measurableEmbedding_aff c hρ) (f := f) (s := aff c ρ '' K)
  rw [Set.preimage_image_eq K (f := aff c ρ) (affH c hρ.ne').injective] at h2
  have h3 := h2.2 hf
  unfold IntegrableOn at h3 ⊢
  rw [Measure.restrict_smul, integrable_smul_measure (sc_ne_zero hρ) sc_ne_top] at h3
  exact h3

theorem locallyIntegrableOn_comp (hρ : 0 < ρ) (h : IsAff Ω V c ρ) {F : Type*}
    [NormedAddCommGroup F] {f : R3 → F} (hf : LocallyIntegrableOn f Ω volume) :
    LocallyIntegrableOn (fun x => f (c + ρ • x)) V volume := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hf
  rw [locallyIntegrableOn_iff V.isOpen.isLocallyClosed]
  intro K hK hKc
  refine integrableOn_comp hρ (hf _ ?_ (hKc.image (continuous_aff c ρ)))
  rintro _ ⟨x, hx, rfl⟩
  exact (h x).2 (hK hx)

theorem hasWeakLineDerivOn_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hρ : 0 < ρ) (h : IsAff Ω V c ρ) {u u' : R3 → F} {v : R3}
    (hu : HasWeakLineDerivOn volume Ω u u' (ρ • v)) :
    HasWeakLineDerivOn volume V (fun x => u (c + ρ • x)) (fun x => u' (c + ρ • x)) v := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨hu.completeSpace, locallyIntegrableOn_comp hρ h hu.locallyIntegrableOn,
    locallyIntegrableOn_comp hρ h hu.locallyIntegrableOn_deriv, fun φ => ?_⟩
  have hρ' : 0 < ρ⁻¹ := inv_pos.2 hρ
  let ψ : 𝓓(Ω, ℝ) := compTest hρ' (isAff_symm hρ h) φ
  have hψ : ∀ x, (ψ : R3 → ℝ) (c + ρ • x) = φ x := by
    intro x
    simp only [ψ, compTest_apply]
    rw [show c + ρ • x = c + ρ • x + 0 by rw [add_zero], aff_symm_aff hρ, smul_zero, add_zero]
  have hleft : (∫ x, lineDeriv ℝ (φ : R3 → ℝ) x v • u (c + ρ • x)) =
      (sc ρ).toReal⁻¹ • ∫ y, lineDeriv ℝ (ψ : R3 → ℝ) y (ρ • v) • u y := by
    rw [← integral_comp_aff c hρ]
    congr 1; funext x; congr 1
    simp only [lineDeriv, ψ, compTest_apply]
    congr 1; funext t
    rw [smul_smul, mul_comm, ← smul_smul, aff_symm_aff hρ, smul_smul, inv_mul_cancel₀ hρ.ne',
      one_smul]
  have hright : (∫ x, (φ : R3 → ℝ) x • u' (c + ρ • x)) =
      (sc ρ).toReal⁻¹ • ∫ y, (ψ : R3 → ℝ) y • u' y := by
    rw [← integral_comp_aff c hρ]
    simp only [hψ]
  rw [hleft, hright, hu.integral_lineDeriv_smul_eq_neg_integral_smul ψ, smul_neg]

theorem hasWeakFDerivOn_comp (hρ : 0 < ρ) (h : IsAff Ω V c ρ) {u : R3 → ℝ} {g : R3 → R3}
    (hu : HasWeakFDerivOn volume Ω u (fun x => innerSL ℝ (g x))) :
    HasWeakFDerivOn volume V (fun x => u (c + ρ • x))
      (fun x => innerSL ℝ (ρ • g (c + ρ • x))) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  have h1 := hasWeakLineDerivOn_comp hρ h ((hasWeakFDerivOn_iff.1 hu) (ρ • v))
  have heq : (fun x => innerSL ℝ (ρ • g (c + ρ • x)) v) =
      fun x => innerSL ℝ (g (c + ρ • x)) (ρ • v) := by
    funext x
    simp only [innerSL_apply_apply, real_inner_smul_left, real_inner_smul_right]
  rw [heq]
  exact h1

/-! ### The first-order pullback -/

theorem hasWeakFDerivOn_pull1 (hρ : 0 < ρ) (h : IsAff Ω V c ρ)
    (u : W1p (volume : Measure R3) Ω 2) :
    HasWeakFDerivOn volume V (compL hρ h (W1p.value u))
      (fun x => innerSL ℝ ((ρ • compL hρ h (W1p.gradient u) :
        Lp R3 2 ((volume : Measure R3).restrict V)) x)) := by
  have h1 := hasWeakFDerivOn_comp hρ h (W1p.hasWeakFDerivOn u)
  refine (h1.congr_ae (compL_ae hρ h _).symm).congr_ae_deriv ?_
  filter_upwards [Lp.coeFn_smul ρ (compL hρ h (W1p.gradient u)),
    compL_ae hρ h (W1p.gradient u)] with x h2 h3
  rw [h2, Pi.smul_apply, h3]

/-- The first-order pullback, unbundled. -/
def pull1Fun (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (u : W1p (volume : Measure R3) Ω 2) :
    W1p (volume : Measure R3) V 2 :=
  W1p.mk (compL hρ h (W1p.value u)) (ρ • compL hρ h (W1p.gradient u)) (hasWeakFDerivOn_pull1 hρ h u)

theorem value_pull1Fun (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (u : W1p (volume : Measure R3) Ω 2) :
    W1p.value (pull1Fun hρ h u) = compL hρ h (W1p.value u) := W1p.value_mk _ _ _

theorem gradient_pull1Fun (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (u : W1p (volume : Measure R3) Ω 2) :
    W1p.gradient (pull1Fun hρ h u) = ρ • compL hρ h (W1p.gradient u) := W1p.gradient_mk _ _ _

theorem w1_value_add {U : Opens R3} (u v : W1p (volume : Measure R3) U 2) :
    W1p.value (u + v) = W1p.value u + W1p.value v := map_add W1p.valueL u v

theorem w1_gradient_add {U : Opens R3} (u v : W1p (volume : Measure R3) U 2) :
    W1p.gradient (u + v) = W1p.gradient u + W1p.gradient v := map_add W1p.gradientL u v

theorem w1_value_smul {U : Opens R3} (a : ℝ) (u : W1p (volume : Measure R3) U 2) :
    W1p.value (a • u) = a • W1p.value u := map_smul W1p.valueL a u

theorem w1_gradient_smul {U : Opens R3} (a : ℝ) (u : W1p (volume : Measure R3) U 2) :
    W1p.gradient (a • u) = a • W1p.gradient u := map_smul W1p.gradientL a u

theorem norm_compL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (hρ : 0 < ρ)
    (h : IsAff Ω V c ρ) (f : Lp F 2 ((volume : Measure R3).restrict Ω)) :
    ‖compL hρ h f‖ = kC ρ * ‖f‖ := norm_compLm hρ h f

theorem pull1Fun_smul (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (a : ℝ)
    (u : W1p (volume : Measure R3) Ω 2) : pull1Fun hρ h (a • u) = a • pull1Fun hρ h u := by
  apply W1p.ext
  · conv_lhs => rw [value_pull1Fun hρ h, w1_value_smul a u]
    conv_rhs => rw [w1_value_smul a (pull1Fun hρ h u), value_pull1Fun hρ h]
    exact (compL hρ h).map_smul a (W1p.value u)
  · conv_lhs => rw [gradient_pull1Fun hρ h, w1_gradient_smul a u,
      (compL hρ h).map_smul a (W1p.gradient u)]
    conv_rhs => rw [w1_gradient_smul a (pull1Fun hρ h u), gradient_pull1Fun hρ h]
    exact smul_comm ρ a _

/-- The first-order pullback as a linear map. -/
def pull1Lm (hρ : 0 < ρ) (h : IsAff Ω V c ρ) :
    W1p (volume : Measure R3) Ω 2 →ₗ[ℝ] W1p (volume : Measure R3) V 2 where
  toFun := pull1Fun hρ h
  map_add' u v := by
    apply W1p.ext
    · rw [w1_value_add, value_pull1Fun, value_pull1Fun, value_pull1Fun, w1_value_add, map_add]
    · rw [w1_gradient_add, gradient_pull1Fun, gradient_pull1Fun, gradient_pull1Fun,
        w1_gradient_add, map_add, smul_add]
  map_smul' a u := pull1Fun_smul hρ h a u

theorem kC_nonneg (ρ : ℝ) : 0 ≤ kC ρ := ENNReal.toReal_nonneg

theorem norm_pull1Fun_le (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (u : W1p (volume : Measure R3) Ω 2) :
    ‖pull1Fun hρ h u‖ ≤ (kC ρ + ‖ρ‖ * kC ρ) * ‖u‖ := by
  refine (W1p.norm_le_norm_value_add_norm_gradient _).trans ?_
  rw [value_pull1Fun, gradient_pull1Fun, norm_smul, norm_compL hρ h, norm_compL hρ h]
  have := kC_nonneg ρ
  have h1 := W1p.norm_value_le u
  have h2 := W1p.norm_gradient_le u
  calc kC ρ * ‖W1p.value u‖ + ‖ρ‖ * (kC ρ * ‖W1p.gradient u‖)
      ≤ kC ρ * ‖u‖ + ‖ρ‖ * (kC ρ * ‖u‖) := by gcongr
    _ = _ := by ring

/-- The first-order pullback `u ↦ u (c + ρ •)`. -/
def pull1 (hρ : 0 < ρ) (h : IsAff Ω V c ρ) :
    W1p (volume : Measure R3) Ω 2 →L[ℝ] W1p (volume : Measure R3) V 2 :=
  (pull1Lm hρ h).mkContinuous _ (norm_pull1Fun_le hρ h)

theorem pull1_apply (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (u : W1p (volume : Measure R3) Ω 2) :
    pull1 hρ h u = pull1Fun hρ h u := rfl

/-! ### Higher order -/

/-- Compatibility of an order-`k` operator with composition on values. -/
def ValueCompat (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k) : Prop :=
  ∀ u, Wkp.value k (L u) = compL hρ h (Wkp.value k u)

theorem partials_hyp (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k)
    (hL : ValueCompat hρ h k L) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) (i : Fin 3) :
    ⇑(Wkp.value k (ρ • L (WkpCalculus.dL i k u))) =ᵐ[(volume : Measure R3).restrict V]
      fun x => W1p.gradient (pull1 hρ h (Wkp.firstOrder k u)) x i := by
  rw [Wkp.value_smul, hL, pull1_apply, gradient_pull1Fun]
  filter_upwards [Lp.coeFn_smul ρ (compL hρ h (Wkp.value k (WkpCalculus.dL i k u))),
    compL_ae hρ h (Wkp.value k (WkpCalculus.dL i k u)),
    (qmp hρ h).ae (WkpCalculus.value_d i k u),
    Lp.coeFn_smul ρ (compL hρ h (W1p.gradient (Wkp.firstOrder k u))),
    compL_ae hρ h (W1p.gradient (Wkp.firstOrder k u))] with x h1 h2 h3 h4 h5
  rw [h1, Pi.smul_apply, h2, WkpCalculus.dL_apply, h4, Pi.smul_apply, h5, PiLp.smul_apply]
  exact congrArg (ρ • ·) h3

/-- The order-`k+1` pullback built from the order-`k` one. -/
def pullSuccFun (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k)
    (hL : ValueCompat hρ h k L) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    Wkp (volume : Measure R3) V 2 (k + 1) :=
  WkpCalculus.ofPartials k (pull1 hρ h (Wkp.firstOrder k u))
    (fun i => ρ • L (WkpCalculus.dL i k u)) (partials_hyp hρ h k L hL u)

theorem value_pullSuccFun (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k)
    (hL : ValueCompat hρ h k L) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    Wkp.value (k + 1) (pullSuccFun hρ h k L hL u) = compL hρ h (Wkp.value (k + 1) u) := by
  rw [pullSuccFun, WkpCalculus.value_ofPartials, pull1_apply, value_pull1Fun,
    Wkp.value_firstOrder]

theorem firstOrder_pullSuccFun (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k)
    (hL : ValueCompat hρ h k L) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    Wkp.firstOrder k (pullSuccFun hρ h k L hL u) = pull1 hρ h (Wkp.firstOrder k u) :=
  WkpCalculus.firstOrder_ofPartials _ _ _ _

theorem pullSuccFun_add (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k)
    (hL : ValueCompat hρ h k L) (u v : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    pullSuccFun hρ h k L hL (u + v) = pullSuccFun hρ h k L hL u + pullSuccFun hρ h k L hL v := by
  apply Wkp.ext (k + 1)
  conv_lhs => rw [value_pullSuccFun, Wkp.value_add, map_add]
  conv_rhs => rw [Wkp.value_add, value_pullSuccFun, value_pullSuccFun]

theorem pullSuccFun_smul (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k)
    (hL : ValueCompat hρ h k L) (a : ℝ) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    pullSuccFun hρ h k L hL (a • u) = a • pullSuccFun hρ h k L hL u := by
  apply Wkp.ext (k + 1)
  conv_lhs => rw [value_pullSuccFun, Wkp.value_smul, map_smul]
  conv_rhs => rw [Wkp.value_smul, value_pullSuccFun]

/-- The bound constant at order `k + 1`. -/
def succC (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k) : ℝ :=
  ‖pull1 hρ h‖ * ‖Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := Ω) (p := 2) k‖ +
    k * ∑ i : Fin 3, ‖ρ‖ * (‖L‖ * ‖WkpCalculus.dL (Ω := Ω) i k‖)

theorem norm_pullSuccFun_le (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k)
    (hL : ValueCompat hρ h k L) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    ‖pullSuccFun hρ h k L hL u‖ ≤ succC hρ h k L * ‖u‖ := by
  refine (WkpCalculus.norm_ofPartials_le _ _ _ _).trans ?_
  have h1 : ‖pull1 hρ h (Wkp.firstOrder k u)‖ ≤
      ‖pull1 hρ h‖ * ‖Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := Ω) (p := 2) k‖ *
        ‖u‖ := by
    rw [mul_assoc, ← Wkp.firstOrderL_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
  have h2 : ∀ i : Fin 3, ‖ρ • L (WkpCalculus.dL i k u)‖ ≤
      ‖ρ‖ * (‖L‖ * ‖WkpCalculus.dL (Ω := Ω) i k‖) * ‖u‖ := by
    intro i
    rw [norm_smul, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
  have h3 : ∑ i : Fin 3, ‖ρ • L (WkpCalculus.dL i k u)‖ ≤
      (∑ i : Fin 3, ‖ρ‖ * (‖L‖ * ‖WkpCalculus.dL (Ω := Ω) i k‖)) * ‖u‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => h2 i
  rw [succC, add_mul, mul_assoc (k : ℝ)]
  exact add_le_add h1 (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg k))

/-- The order-`k+1` pullback as a continuous linear map. -/
def pullSucc (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k)
    (hL : ValueCompat hρ h k L) :
    Wkp (volume : Measure R3) Ω 2 (k + 1) →L[ℝ] Wkp (volume : Measure R3) V 2 (k + 1) :=
  LinearMap.mkContinuous
    { toFun := pullSuccFun hρ h k L hL
      map_add' := pullSuccFun_add hρ h k L hL
      map_smul' := pullSuccFun_smul hρ h k L hL }
    (succC hρ h k L) (norm_pullSuccFun_le hρ h k L hL)

theorem pullSucc_apply (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k)
    (hL : ValueCompat hρ h k L) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    pullSucc hρ h k L hL u = pullSuccFun hρ h k L hL u := rfl

/-- The pullback at every order, bundled with its value compatibility. -/
def pullPack (hρ : 0 < ρ) (h : IsAff Ω V c ρ) : (k : ℕ) →
    {L : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k //
      ValueCompat hρ h k L}
  | 0 => ⟨compL hρ h, fun _ => rfl⟩
  | k + 1 => ⟨pullSucc hρ h k (pullPack hρ h k).1 (pullPack hρ h k).2,
      fun u => value_pullSuccFun hρ h k (pullPack hρ h k).1 (pullPack hρ h k).2 u⟩

/-- The pullback `u ↦ u (c + ρ •)` at order `k`. -/
def pullL (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ) :
    Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) V 2 k :=
  (pullPack hρ h k).1

theorem value_pullL (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (u : Wkp (volume : Measure R3) Ω 2 k) :
    Wkp.value k (pullL hρ h k u) = compL hρ h (Wkp.value k u) := (pullPack hρ h k).2 u

theorem firstOrder_pullL (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (u : Wkp (volume : Measure R3) Ω 2 (k + 1)) :
    Wkp.firstOrder k (pullL hρ h (k + 1) u) = pull1 hρ h (Wkp.firstOrder k u) :=
  firstOrder_pullSuccFun hρ h k (pullPack hρ h k).1 (pullPack hρ h k).2 u

theorem pullL_one (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (u : W1p (volume : Measure R3) Ω 2) :
    (pullL hρ h 1 u : W1p (volume : Measure R3) V 2) = pull1 hρ h u := by
  exact firstOrder_pullL hρ h 0 u

/-! ### Inverses -/

theorem aff_symm_aff_zero (hρ : 0 < ρ) (x : R3) : -(ρ⁻¹ • c) + ρ⁻¹ • (c + ρ • x) = x := by
  have := aff_symm_aff (c := c) hρ x 0
  rwa [add_zero, smul_zero, add_zero] at this

theorem compL_symm_compL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (hρ : 0 < ρ)
    (h : IsAff Ω V c ρ) (f : Lp F 2 ((volume : Measure R3).restrict Ω)) :
    compL (inv_pos.2 hρ) (isAff_symm hρ h) (compL hρ h f) = f := by
  apply Lp.ext
  filter_upwards [compL_ae (inv_pos.2 hρ) (isAff_symm hρ h) (compL hρ h f),
    (qmp (inv_pos.2 hρ) (isAff_symm hρ h)).ae (compL_ae hρ h f)] with x h1 h2
  rw [h1]
  rw [aff_apply] at h2
  rw [h2, aff_aff_symm hρ]

theorem compL_compL_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (hρ : 0 < ρ)
    (h : IsAff Ω V c ρ) (f : Lp F 2 ((volume : Measure R3).restrict V)) :
    compL hρ h (compL (inv_pos.2 hρ) (isAff_symm hρ h) f) = f := by
  apply Lp.ext
  filter_upwards [compL_ae hρ h (compL (inv_pos.2 hρ) (isAff_symm hρ h) f),
    (qmp hρ h).ae (compL_ae (inv_pos.2 hρ) (isAff_symm hρ h) f)] with x h1 h2
  rw [h1]
  rw [aff_apply] at h2
  rw [h2, aff_symm_aff_zero hρ]

theorem pullL_symm_pullL (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (u : Wkp (volume : Measure R3) Ω 2 k) :
    pullL (inv_pos.2 hρ) (isAff_symm hρ h) k (pullL hρ h k u) = u := by
  apply Wkp.ext k
  rw [value_pullL, value_pullL, compL_symm_compL]

theorem pullL_pullL_symm (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (k : ℕ)
    (u : Wkp (volume : Measure R3) V 2 k) :
    pullL hρ h k (pullL (inv_pos.2 hρ) (isAff_symm hρ h) k u) = u := by
  apply Wkp.ext k
  rw [value_pullL, value_pullL, compL_compL_symm]

/-! ### `H¹₀` -/

theorem pull1_ofTestFunction (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (φ : 𝓓(Ω, ℝ)) :
    pull1 hρ h (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      W1p.ofTestFunctionₗ volume V 2 (compTest hρ h φ) := by
  apply W1p.ext_value
  rw [pull1_apply, value_pull1Fun, W1p.value_ofTestFunctionₗ, W1p.value_ofTestFunctionₗ]
  apply Lp.ext
  filter_upwards [compL_ae hρ h (testFunctionLp (mu := (volume : Measure R3)) 2 φ),
    (qmp hρ h).ae (testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ),
    testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 (compTest hρ h φ)] with x h1 h2 h3
  rw [h1, h3]
  exact h2

theorem pull1_mem_w1p0 (hρ : 0 < ρ) (h : IsAff Ω V c ρ) {u : W1p (volume : Measure R3) Ω 2}
    (hu : u ∈ w1p0Submodule (volume : Measure R3) Ω 2) :
    pull1 hρ h u ∈ w1p0Submodule (volume : Measure R3) V 2 := by
  have hclosed : IsClosed ((pull1 hρ h) ⁻¹'
      (w1p0Submodule (volume : Measure R3) V 2 : Set (W1p (volume : Measure R3) V 2))) :=
    (w1p0Submodule (volume : Measure R3) V 2).isClosed.preimage (pull1 hρ h).continuous
  have hsub := w1p0Submodule_subset_of_isClosed hclosed (fun φ => by
    refine Set.mem_preimage.2 (SetLike.mem_coe.2 ?_)
    rw [pull1_ofTestFunction]
    exact W1p.ofTestFunctionₗ_mem_w1p0Submodule _)
  exact SetLike.mem_coe.1 (Set.mem_preimage.1 (hsub (SetLike.mem_coe.2 hu)))

theorem pull1_symm_pull1 (hρ : 0 < ρ) (h : IsAff Ω V c ρ) (u : W1p (volume : Measure R3) Ω 2) :
    pull1 (inv_pos.2 hρ) (isAff_symm hρ h) (pull1 hρ h u) = u := by
  apply W1p.ext_value
  rw [pull1_apply, value_pull1Fun, pull1_apply, value_pull1Fun, compL_symm_compL]

/-! ### The ball -/

theorem isAff_ball (c : R3) (hρ : 0 < ρ) : IsAff (ballO c ρ) ballOpens c ρ := by
  intro x
  change c + ρ • x ∈ ball c ρ ↔ x ∈ ball (0 : R3) 1
  rw [mem_ball, mem_ball, dist_eq_norm, dist_zero_right, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hρ]
  constructor
  · intro hx; nlinarith [norm_nonneg x]
  · intro hx; nlinarith [norm_nonneg x]

/-- Pullback `u ↦ u (c + ρ •)` from `W^{k,2}(ball c ρ)` to `W^{k,2}(B)`, a continuous linear
equivalence. -/
def pullWkp (c : R3) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    Wkp (volume : Measure R3) (ballO c ρ) 2 k ≃L[ℝ] Wkp (volume : Measure R3) ballOpens 2 k :=
  ContinuousLinearEquiv.equivOfInverse (pullL hρ (isAff_ball c hρ) k)
    (pullL (inv_pos.2 hρ) (isAff_symm hρ (isAff_ball c hρ)) k)
    (pullL_symm_pullL hρ (isAff_ball c hρ) k) (pullL_pullL_symm hρ (isAff_ball c hρ) k)

theorem value_pullWkp (c : R3) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ)
    (u : Wkp (volume : Measure R3) (ballO c ρ) 2 k) :
    ⇑(Wkp.value k (pullWkp c hρ k u)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun y => Wkp.value k u (c + ρ • y) := by
  rw [show pullWkp c hρ k u = pullL hρ (isAff_ball c hρ) k u from rfl, value_pullL]
  exact compL_ae hρ (isAff_ball c hρ) _

theorem value_pullWkp_symm (c : R3) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ)
    (v : Wkp (volume : Measure R3) ballOpens 2 k) :
    ⇑(Wkp.value k ((pullWkp c hρ k).symm v)) =ᵐ[(volume : Measure R3).restrict (ballO c ρ)]
      fun x => Wkp.value k v (ρ⁻¹ • (x - c)) := by
  rw [show (pullWkp c hρ k).symm v =
      pullL (inv_pos.2 hρ) (isAff_symm hρ (isAff_ball c hρ)) k v from rfl, value_pullL]
  filter_upwards [compL_ae (inv_pos.2 hρ) (isAff_symm hρ (isAff_ball c hρ))
    (Wkp.value k v)] with x hx
  rw [hx, smul_sub, sub_eq_neg_add]

/-- At order one the gradient transforms by the factor `ρ`. -/
theorem gradient_pullWkp_one (c : R3) {ρ : ℝ} (hρ : 0 < ρ)
    (u : W1p (volume : Measure R3) (ballO c ρ) 2) :
    ⇑(W1p.gradient (pullWkp c hρ 1 u : W1p (volume : Measure R3) ballOpens 2))
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun y => ρ • W1p.gradient u (c + ρ • y) := by
  rw [show (pullWkp c hρ 1 u : W1p (volume : Measure R3) ballOpens 2) =
      pull1 hρ (isAff_ball c hρ) u from pullL_one hρ _ u, pull1_apply, gradient_pull1Fun]
  filter_upwards [Lp.coeFn_smul ρ (compL hρ (isAff_ball c hρ) (W1p.gradient u)),
    compL_ae hρ (isAff_ball c hρ) (W1p.gradient u)] with x h1 h2
  rw [h1, Pi.smul_apply, h2]

/-- The pullback preserves `H¹₀` (in both directions). -/
theorem pullWkp_one_mem_w1p0_iff (c : R3) {ρ : ℝ} (hρ : 0 < ρ)
    (u : W1p (volume : Measure R3) (ballO c ρ) 2) :
    (pullWkp c hρ 1 u : W1p (volume : Measure R3) ballOpens 2) ∈
        w1p0Submodule (volume : Measure R3) ballOpens 2 ↔
      u ∈ w1p0Submodule (volume : Measure R3) (ballO c ρ) 2 := by
  rw [show (pullWkp c hρ 1 u : W1p (volume : Measure R3) ballOpens 2) =
      pull1 hρ (isAff_ball c hρ) u from pullL_one hρ _ u]
  constructor
  · intro hu
    have := pull1_mem_w1p0 (inv_pos.2 hρ) (isAff_symm hρ (isAff_ball c hρ)) hu
    rwa [pull1_symm_pull1] at this
  · exact pull1_mem_w1p0 hρ (isAff_ball c hρ)

end OAI.AnisotropicCalderon.Affine
