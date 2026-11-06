import Calderon.CollaboratorWkpCalculusOct17
import Calderon.CollaboratorTangentialToH2Oct17
import TauCeti.Analysis.Sobolev.TestFunctionLp
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Second weak derivatives of `H²(B)` functions: symmetry, the strong form of a divergence-form
equation, and related identities (helper for task 05, higher orders). -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.SD
open TauCeti TauCeti.PDE EnergyBridge

variable (V : Wkp (volume : Measure R3) ballOpens 2 2)

/-- `∂_k v` as an element of `W^{1,2}(B)`, where `v = lowerOrder 1 V`. -/
def dv (k : Fin 3) : W1p (volume : Measure R3) ballOpens 2 := Wkp.firstOrder 0 (WkpCalculus.d k 1 V)

theorem value_dv (k : Fin 3) :
    ⇑(W1p.value (dv V k)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => W1p.gradient (Wkp.lowerOrder 1 V) x k := by
  have h := WkpCalculus.value_d k 1 V
  rw [dv, Wkp.value_firstOrder]
  exact h

/-- The second weak derivative `∂_i ∂_k v`. -/
def sd (i k : Fin 3) : R3 → ℝ := fun x => W1p.gradient (dv V k) x i

lemma memLp_coord (G : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) (k : Fin 3) :
    MemLp (fun x => G x k) 2 ((volume : Measure R3).restrict ballOpens) :=
  (EuclideanSpace.proj k : R3 →L[ℝ] ℝ).comp_memLp' (Lp.memLp G)

lemma li_coord (G : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) (k : Fin 3) :
    LocallyIntegrableOn (fun x => G x k) (ballOpens : Set R3) volume :=
  TangH2.locallyIntegrableOn_of_memLp (memLp_coord G k)

lemma li_W (k : Fin 3) :
    LocallyIntegrableOn (fun x => W1p.gradient (Wkp.lowerOrder 1 V) x k) (ballOpens : Set R3) volume :=
  li_coord _ k

lemma li_sd (i k : Fin 3) : LocallyIntegrableOn (sd V i k) (ballOpens : Set R3) volume :=
  li_coord _ i

/-- `∂ᵢ (∂ₖ v) = sd i k` weakly. -/
lemma hasWeakLineDerivOn_W (i k : Fin 3) :
    HasWeakLineDerivOn volume ballOpens (fun x => W1p.gradient (Wkp.lowerOrder 1 V) x k)
      (sd V i k) (TangH2.e i) := by
  refine (((W1p.hasWeakFDerivOn (dv V k)) (TangH2.e i)).congr_ae (value_dv V k)).congr_ae_deriv ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [innerSL_apply_apply, sd]
  rw [TangH2.coord_eq_inner]

lemma integral_W_eq (i k : Fin 3) (φ : 𝓓(ballOpens, ℝ)) :
    ∫ x, lineDeriv ℝ (φ : R3 → ℝ) x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k =
      -∫ x, φ x * sd V i k x := by
  simpa only [smul_eq_mul] using
    (hasWeakLineDerivOn_W V i k).integral_lineDeriv_smul_eq_neg_integral_smul φ

/-- Fundamental lemma on the ball. -/
lemma ae_zero_of_integral {g : R3 → ℝ} (hg : LocallyIntegrableOn g (ballOpens : Set R3) volume)
    (h : ∀ φ : 𝓓(ballOpens, ℝ), ∫ x, φ x * g x = 0) :
    g =ᵐ[(volume : Measure R3).restrict ballOpens] 0 := by
  have H : HasWeakLineDerivOn volume ballOpens (0 : R3 → ℝ) g (TangH2.e 0) := by
    rw [hasWeakLineDerivOn_iff_testFunction]
    refine ⟨inferInstance, locallyIntegrableOn_zero, hg, fun φ => ?_⟩
    simp only [Pi.zero_apply, smul_eq_mul, mul_zero, integral_zero, h φ, neg_zero]
  exact H.ae_eq hasWeakLineDerivOn_zero

theorem sd_symm (i k : Fin 3) :
    sd V i k =ᵐ[(volume : Measure R3).restrict ballOpens] sd V k i := by
  have H : HasWeakLineDerivOn volume ballOpens (fun x => W1p.gradient (Wkp.lowerOrder 1 V) x k)
      (sd V k i) (TangH2.e i) := by
    rw [hasWeakLineDerivOn_iff_testFunction]
    refine ⟨inferInstance, li_W V k, li_sd V k i, fun φ => ?_⟩
    have hs := TangH2.Tf_symm (W1p.hasWeakFDerivOn (Wkp.lowerOrder 1 V)) (li_W V) i k
    have h1 := congrArg (fun T => T φ) hs
    simp only [TangH2.Tf_apply (li_W V _)] at h1
    simp only [smul_eq_mul]
    rw [h1, integral_W_eq]
  exact (hasWeakLineDerivOn_W V i k).ae_eq H


lemma integrable_test_mul {g : R3 → ℝ} (hg : LocallyIntegrableOn g (ballOpens : Set R3) volume)
    (φ : 𝓓(ballOpens, ℝ)) : Integrable (fun x => φ x * g x) volume := by
  simpa [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hg φ

lemma ibp_ik {c : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (φ : 𝓓(ballOpens, ℝ)) (i k : Fin 3) :
    ∫ x, lineDeriv ℝ (φ : R3 → ℝ) x (TangH2.e i) * (c x * W1p.gradient (Wkp.lowerOrder 1 V) x k) =
      -∫ x, (fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k +
        c x * sd V i k x) * φ x := by
  have hdc := TangH2.contDiff_fderiv_apply hc (TangH2.e i)
  have h := congrArg (fun T => T φ) (TangH2.mulF_Tf hc (li_W V k) i)
  simp only [TangH2.mulF, LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply] at h
  rw [TangH2.Tf_apply (li_W V k), TangH2.Tf_apply (TangH2.locallyIntegrableOn_mul hc.continuous (li_W V k)),
    TangH2.Pf_apply (li_W V k), integral_W_eq] at h
  have h1 : ∫ x, (TangH2.mulM c φ) x * sd V i k x = ∫ x, φ x * (c x * sd V i k x) := by
    congr 1; funext x; rw [TangH2.mulM_apply hc]; ring
  have h2 : ∫ x, (TangH2.mulM (fun x => fderiv ℝ c x (TangH2.e i)) φ) x *
      W1p.gradient (Wkp.lowerOrder 1 V) x k =
      ∫ x, φ x * (fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k) := by
    congr 1; funext x; rw [TangH2.mulM_apply hdc]; ring
  rw [h1, h2] at h
  have i1 := integrable_test_mul (TangH2.locallyIntegrableOn_mul hc.continuous (li_sd V i k)) φ
  have i2 := integrable_test_mul (TangH2.locallyIntegrableOn_mul hdc.continuous (li_W V k)) φ
  have h3 : ∫ x, (fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k +
        c x * sd V i k x) * φ x =
      (∫ x, φ x * (fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k)) +
        ∫ x, φ x * (c x * sd V i k x) := by
    rw [← integral_add i2 i1]; congr 1; funext x; ring
  rw [h3]; linarith


lemma setIntegral_test_eq {g : R3 → ℝ} (φ : 𝓓(ballOpens, ℝ)) :
    ∫ x in (ballOpens : Set R3), g x * φ x = ∫ x, g x * φ x := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem), mul_zero]

/-- Integration by parts of `∫ ∇φ · M ∇v` for a smooth matrix field `M`. -/
theorem integral_mbf_eq {M : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hM : ContDiff ℝ ∞ M)
    (φ : 𝓓(ballOpens, ℝ)) :
    ∫ x in (ballOpens : Set R3), matrixBilinearForm (M x) (gradient (φ : R3 → ℝ) x)
        (W1p.gradient (Wkp.lowerOrder 1 V) x) =
      -∫ x in (ballOpens : Set R3),
        (∑ i, ∑ k, (fderiv ℝ (fun y => M y i k) x (EuclideanSpace.single i 1) *
            W1p.gradient (Wkp.lowerOrder 1 V) x k + M x i k * sd V i k x)) * φ x := by
  have hA := TangH2.contDiff_entry hM
  have hawl : ∀ i k, LocallyIntegrableOn
      (fun x => M x i k * W1p.gradient (Wkp.lowerOrder 1 V) x k) (ballOpens : Set R3) volume :=
    fun i k => TangH2.locallyIntegrableOn_mul (hA i k).continuous (li_W V k)
  have hint : ∀ i k, Integrable (fun x => lineDeriv ℝ (φ : R3 → ℝ) x (TangH2.e i) *
      (M x i k * W1p.gradient (Wkp.lowerOrder 1 V) x k)) volume := fun i k => by
    simpa [smul_eq_mul] using integrable_lineDeriv_smul_of_locallyIntegrableOn (hawl i k) φ (TangH2.e i)
  have hint2 : ∀ i k, Integrable (fun x => (fderiv ℝ (fun y => M y i k) x (EuclideanSpace.single i 1) *
      W1p.gradient (Wkp.lowerOrder 1 V) x k + M x i k * sd V i k x) * φ x) volume := fun i k => by
    have hli : LocallyIntegrableOn (fun x => fderiv ℝ (fun y => M y i k) x (EuclideanSpace.single i 1) *
        W1p.gradient (Wkp.lowerOrder 1 V) x k + M x i k * sd V i k x)
        (ballOpens : Set R3) volume :=
      (TangH2.locallyIntegrableOn_mul (TangH2.contDiff_fderiv_apply (hA i k) (EuclideanSpace.single i 1)).continuous
        (li_W V k)).add (TangH2.locallyIntegrableOn_mul (hA i k).continuous (li_sd V i k))
    simpa [mul_comm] using integrable_test_mul hli φ
  have hL : ∑ i, ∑ k, ∫ x, lineDeriv ℝ (φ : R3 → ℝ) x (TangH2.e i) *
        (M x i k * W1p.gradient (Wkp.lowerOrder 1 V) x k) =
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (M x) (gradient (φ : R3 → ℝ) x)
        (W1p.gradient (Wkp.lowerOrder 1 V) x) := by
    rw [Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun k _ => hint i k).symm]
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint i k]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (ballOpens : Set R3))]
    · refine setIntegral_congr_fun ballOpens.isOpen.measurableSet fun x _ => ?_
      have hφx : DifferentiableAt ℝ (φ : R3 → ℝ) x := (φ.contDiff.differentiable (by simp)) x
      simp only [TangH2.matrixBilinearForm_eq_sum, TangH2.gradient_coord hφx]
    · intro x hx
      have hnot : x ∉ tsupport (φ : R3 → ℝ) := fun hmem => hx (φ.tsupport_subset hmem)
      simp [lineDeriv_eq_zero_of_notMem_tsupport φ hnot]
  rw [← hL, setIntegral_test_eq]
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint2 i k]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ => hint2 i k, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact ibp_ik V (hA i k) φ i k


lemma li_sum {ι : Type*} (s : Finset ι) {f : ι → R3 → ℝ}
    (h : ∀ i ∈ s, LocallyIntegrableOn (f i) (ballOpens : Set R3) volume) :
    LocallyIntegrableOn (fun x => ∑ i ∈ s, f i x) (ballOpens : Set R3) volume := by
  have := Finset.sum_induction f (fun g => LocallyIntegrableOn g (ballOpens : Set R3) volume)
    (fun _ _ => LocallyIntegrableOn.add) locallyIntegrableOn_zero h
  simpa only [← Finset.sum_apply] using this

/-- The strong form of `-div(a ∇v) = F`. -/
theorem strong_form {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    (heq : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient (Wkp.lowerOrder 1 V) x) =
        ∫ x in (ballOpens : Set R3), F x * φ x) :
    (fun x => ∑ i, ∑ k, a x i k * sd V i k x) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => -F x - ∑ i, ∑ k, fderiv ℝ (fun y => a y i k) x (EuclideanSpace.single i 1) *
        W1p.gradient (Wkp.lowerOrder 1 V) x k := by
  have hA := TangH2.contDiff_entry ha
  have hS : LocallyIntegrableOn (fun x => ∑ i, ∑ k,
      (fderiv ℝ (fun y => a y i k) x (EuclideanSpace.single i 1) *
        W1p.gradient (Wkp.lowerOrder 1 V) x k + a x i k * sd V i k x))
      (ballOpens : Set R3) volume :=
    li_sum _ fun i _ => li_sum _ fun k _ =>
      (TangH2.locallyIntegrableOn_mul (TangH2.contDiff_fderiv_apply (hA i k)
        (EuclideanSpace.single i 1)).continuous (li_W V k)).add
        (TangH2.locallyIntegrableOn_mul (hA i k).continuous (li_sd V i k))
  have hF : LocallyIntegrableOn (fun x => F x) (ballOpens : Set R3) volume :=
    TangH2.locallyIntegrableOn_of_memLp (Lp.memLp F)
  have hz := ae_zero_of_integral (hF.add hS) fun φ => by
    have h1 := (heq φ).symm.trans (integral_mbf_eq V ha φ)
    rw [setIntegral_test_eq, setIntegral_test_eq] at h1
    have i1 := integrable_test_mul hF φ
    have i2 := integrable_test_mul hS φ
    have h2 : ∫ x, φ x * ((fun x => F x) + fun x => ∑ i, ∑ k,
        (fderiv ℝ (fun y => a y i k) x (EuclideanSpace.single i 1) *
          W1p.gradient (Wkp.lowerOrder 1 V) x k + a x i k * sd V i k x)) x =
        (∫ x, F x * φ x) + ∫ x, (∑ i, ∑ k,
        (fderiv ℝ (fun y => a y i k) x (EuclideanSpace.single i 1) *
          W1p.gradient (Wkp.lowerOrder 1 V) x k + a x i k * sd V i k x)) * φ x := by
      rw [← integral_add (by simpa only [mul_comm] using i1) (by simpa only [mul_comm] using i2)]
      congr 1; funext x; simp only [Pi.add_apply]; ring
    rw [h2, h1]; ring
  filter_upwards [hz] with x hx
  simp only [Pi.add_apply, Pi.zero_apply, Finset.sum_add_distrib] at hx
  linarith


/-- The ball of radius `3/4`. -/
def ball34 : Opens R3 := ⟨Metric.ball 0 (3 / 4), Metric.isOpen_ball⟩

lemma ball34_le : ball34 ≤ ballOpens := by
  intro x hx
  change x ∈ Metric.ball (0 : R3) (3 / 4) at hx
  change x ∈ Metric.ball (0 : R3) 1
  rw [Metric.mem_ball] at hx ⊢; linarith

lemma mem_ball34 {x : R3} : x ∈ (ball34 : Set R3) ↔ ‖x‖ < 3 / 4 := by
  change x ∈ Metric.ball (0 : R3) (3 / 4) ↔ _
  rw [Metric.mem_ball, dist_zero_right]

/-- Second derivatives vanish where `v` vanishes (on `B_{3/4}`). -/
theorem sd_eq_zero
    (hv0 : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens,
      ‖x‖ < 3 / 4 → W1p.value (Wkp.lowerOrder 1 V) x = 0) (i k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, ‖x‖ < 3 / 4 → sd V i k x = 0 := by
  have hm := ball34.isOpen.measurableSet
  have hval : ∀ᵐ x ∂(volume : Measure R3).restrict (ball34 : Set R3),
      W1p.value (Wkp.lowerOrder 1 V) x = 0 := by
    have h1 := ae_restrict_of_ae_restrict_of_subset
      (show (ball34 : Set R3) ⊆ ballOpens from ball34_le) hv0
    filter_upwards [h1, ae_restrict_mem (μ := (volume : Measure R3)) hm] with x hx hxV
    exact hx (mem_ball34.mp hxV)
  have hg := W1p.gradient_ae_eq_zero_of_value_ae_eq_zero ball34_le hval
  have hval2 : ∀ᵐ x ∂(volume : Measure R3).restrict (ball34 : Set R3),
      W1p.value (dv V k) x = 0 := by
    have h1 := ae_restrict_of_ae_restrict_of_subset
      (show (ball34 : Set R3) ⊆ ballOpens from ball34_le) (value_dv V k)
    filter_upwards [h1, hg] with x hx hgx
    rw [hx, hgx]; rfl
  have hg2 := W1p.gradient_ae_eq_zero_of_value_ae_eq_zero ball34_le hval2
  rw [ae_restrict_iff' hm] at hg2
  refine ae_restrict_of_ae ?_
  filter_upwards [hg2] with x hx hxr
  simp only [sd, hx (mem_ball34.mpr hxr)]
  rfl


lemma hasWeakLineDerivOn_cW {c : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (i k : Fin 3) :
    HasWeakLineDerivOn volume ballOpens
      (fun x => c x * W1p.gradient (Wkp.lowerOrder 1 V) x k)
      (fun x => fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k +
        c x * sd V i k x) (TangH2.e i) := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, TangH2.locallyIntegrableOn_mul hc.continuous (li_W V k),
    (TangH2.locallyIntegrableOn_mul (TangH2.contDiff_fderiv_apply hc _).continuous
      (li_W V k)).add (TangH2.locallyIntegrableOn_mul hc.continuous (li_sd V i k)),
    fun φ => ?_⟩
  simp only [smul_eq_mul]
  rw [ibp_ik V hc φ i k]
  congr 1; congr 1; funext x; ring

lemma fderiv_coord (j i : Fin 3) (x : R3) :
    fderiv ℝ (fun y : R3 => y j) x (TangH2.e i) = if i = j then 1 else 0 := by
  have h : (fun y : R3 => y j) = ⇑(EuclideanSpace.proj j : R3 →L[ℝ] ℝ) := rfl
  rw [h, ContinuousLinearMap.fderiv]
  simp [TangH2.e, eq_comm]

/-- The gradient of the tangential derivative `z = x_j ∂_k v - x_k ∂_j v`. -/
theorem gradient_tangential {z : W1p (volume : Measure R3) ballOpens 2} (j k : Fin 3)
    (hz : ⇑(W1p.value z) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => x j * W1p.gradient (Wkp.lowerOrder 1 V) x k -
        x k * W1p.gradient (Wkp.lowerOrder 1 V) x j) (i : Fin 3) :
    (fun x => W1p.gradient z x i) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => (if i = j then W1p.gradient (Wkp.lowerOrder 1 V) x k else 0) + x j * sd V i k x -
        (if i = k then W1p.gradient (Wkp.lowerOrder 1 V) x j else 0) - x k * sd V i j x := by
  have H := (hasWeakLineDerivOn_cW V (TangH2.contDiff_coord j) i k).sub
    (hasWeakLineDerivOn_cW V (TangH2.contDiff_coord k) i j)
  have Hz : HasWeakLineDerivOn volume ballOpens (W1p.value z) (fun x => W1p.gradient z x i)
      (TangH2.e i) := by
    refine ((W1p.hasWeakFDerivOn z) (TangH2.e i)).congr_ae_deriv
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [innerSL_apply_apply]
    rw [TangH2.coord_eq_inner]
  have H' := H.congr_ae (u := _) (w := ⇑(W1p.value z))
    (by filter_upwards [hz] with x hx; rw [hx]; rfl)
  filter_upwards [Hz.ae_eq H'] with x hx
  rw [hx]
  simp only [Pi.sub_apply, fderiv_coord]
  split_ifs <;> ring

end OAI.AnisotropicCalderon.Regularity.SD
