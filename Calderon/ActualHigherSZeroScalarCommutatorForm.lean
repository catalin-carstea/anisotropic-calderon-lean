import Calderon.ActualHigherSScalarCommutatorForm
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroScalarCommutatorForm
open PrincipalCommutator ReferenceDensityBounds ActualHigherSScalarCommutatorCoefficients
  ActualHigherSScalarCommutatorForm
section Generic
variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma directional_linear_input (I : E →L[ℝ] G) (u : R3 → E)
    (hu : ContDiff ℝ ∞ u) (X x : R3) :
    directionalFDeriv X (fun y => I (u y)) x = I (directionalFDeriv X u x) := by
  have h := directionalFDeriv_clm_apply X (fun _ : R3 => I) u contDiff_const hu x
  simpa only [directionalFDeriv,fderiv_const_apply,zero_apply,map_zero,zero_add] using h

/-- Move the base derivative off the high input, keeping only the genuine included gradient. -/
theorem weighted_first_operator_green
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (mu : R3 → ℝ)
    (u : R3 → E) (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (X : R3) :
    (∫ x, mu x*P (I (u x)) (C x (directionalFDeriv X u x))) =
      -(∫ x, directionalFDeriv X mu x*P (I (u x)) (C x (u x))+
        mu x*P (I (directionalFDeriv X u x)) (C x (u x))+
        mu x*P (I (u x)) ((directionalFDeriv X C x) (u x))) := by
  let z : R3 → F := fun x => C x (u x)
  let v : R3 → G := fun x => I (u x)
  let f : R3 → G := fun x => mu x • v x
  have hv : ContDiff ℝ ∞ v := contDiff_const.clm_apply hu
  have hz : ContDiff ℝ ∞ z := contDiff_supported_operator_apply u C K hK.isClosed hu h0 hC
  have hzc : HasCompactSupport z := compact_supported_operator_apply u C K hK h0
  have hf : ContDiff ℝ ∞ f := hm.smul hv
  have hfi := compact_bilinear_integrable P _ z (contDiff_directionalFDeriv X f hf).continuous hz.continuous hzc
  have hzi := compact_bilinear_integrable P f _ hf.continuous
    (contDiff_directionalFDeriv X z hz).continuous (hzc.fderiv_apply (𝕜 := ℝ) X)
  have hbase := compact_bilinear_integrable P f z hf.continuous hz.continuous hzc
  have hg := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := P) (v := X) hfi hzi hbase
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hz.differentiable (by simp) x)
  have hzD (x : R3) : directionalFDeriv X z x =
      directionalFDeriv X C x (u x)+C x (directionalFDeriv X u x) :=
    directional_operator_apply_supported u C K hK.isClosed hu h0 hC X x
  have hfD (x : R3) : directionalFDeriv X f x =
      directionalFDeriv X mu x • I (u x)+mu x • I (directionalFDeriv X u x) := by
    have h := directional_smul_at mu v x X hm.contDiffAt hv.contDiffAt
    have hI : directionalFDeriv X v x = I (directionalFDeriv X u x) := directional_linear_input I u hu X x
    rw [hI] at h
    exact h
  let A : R3 → ℝ := fun x => mu x*P (I (u x)) (C x (directionalFDeriv X u x))
  let B : R3 → ℝ := fun x => mu x*P (I (u x)) ((directionalFDeriv X C x) (u x))
  let D : R3 → ℝ := fun x => directionalFDeriv X mu x*P (I (u x)) (C x (u x))+
      mu x*P (I (directionalFDeriv X u x)) (C x (u x))
  have hAB : (fun x => P (f x) (directionalFDeriv X z x)) = fun x => A x+B x := by
    funext x
    rw [hzD x]
    simp only [f,v,A,B,map_smul,smul_apply,smul_eq_mul,map_add]
    ring
  have hD : (fun x => P (directionalFDeriv X f x) (z x)) = D := by
    funext x
    rw [hfD x]
    simp only [D,z,map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  have hBC := contDiff_supported_operator_apply u (directionalFDeriv X C) K hK.isClosed hu h0
    (fun x hx => contDiffAt_directional C x X (hC x hx))
  have hBi : Integrable B := by
    have h := compact_bilinear_integrable P f _ hf.continuous hBC.continuous
      (compact_supported_operator_apply u _ K hK h0)
    convert h using 1
    funext x
    simp only [f,v,B,map_smul,smul_apply,smul_eq_mul]
  have hAi : Integrable A := by
    have h := hzi
    rw [hAB] at h
    exact (h.sub hBi).congr (by filter_upwards [] with x; exact add_sub_cancel_right _ _)
  have hDi : Integrable D := by rw [←hD]; exact hfi
  change (∫ x, A x) = -(∫ x, D x+B x)
  change (∫ x, P (f x) (directionalFDeriv X z x)) =
    -(∫ x, P (directionalFDeriv X f x) (z x)) at hg
  rw [hAB,hD,integral_add hAi hBi] at hg
  rw [integral_add hDi hBi]
  linarith

/-- The exact mixed high-mass / included-gradient energy; no high gradient norm. -/
def inclusionEnergyDensity (I : E →L[ℝ] G) (beta : ℝ) (u : R3 → E) (x : R3) : ℝ :=
  beta⁻¹*(∑ i : Fin 3, ‖I (directionalFDeriv (coordinateDirection i) u x)‖^2)+beta*‖u x‖^2

lemma inclusionEnergyDensity_nonneg (I : E →L[ℝ] G) (beta : ℝ) (u : R3 → E) (x : R3)
    (hb : 0 ≤ beta) : 0 ≤ inclusionEnergyDensity I beta u x := by
  unfold inclusionEnergyDensity
  positivity

lemma inclusion_energy_mass_le (I : E →L[ℝ] G) (beta : ℝ) (u : R3 → E) (x : R3)
    (hb : 1 ≤ beta) : ‖u x‖^2 ≤ inclusionEnergyDensity I beta u x := by
  have h := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖u x‖)
  have hD : 0 ≤ beta⁻¹*(∑ i : Fin 3, ‖I (directionalFDeriv (coordinateDirection i) u x)‖^2) := by positivity
  unfold inclusionEnergyDensity
  nlinarith only [h,hD]

lemma inclusion_energy_mixed_le (I : E →L[ℝ] G) (beta : ℝ) (u : R3 → E) (x : R3)
    (hb : 0 < beta) (i : Fin 3) :
    ‖I (directionalFDeriv (coordinateDirection i) u x)‖*‖u x‖ ≤ inclusionEnergyDensity I beta u x := by
  have hY := mul_nonneg (inv_nonneg.mpr hb.le)
    (sq_nonneg (beta*‖u x‖-‖I (directionalFDeriv (coordinateDirection i) u x)‖))
  have he : beta⁻¹*(beta*‖u x‖-‖I (directionalFDeriv (coordinateDirection i) u x)‖)^2 =
      beta*‖u x‖^2+beta⁻¹*‖I (directionalFDeriv (coordinateDirection i) u x)‖^2-
        2*‖I (directionalFDeriv (coordinateDirection i) u x)‖*‖u x‖ := by
    field_simp [hb.ne'] <;> ring
  rw [he] at hY
  have hd := Finset.single_le_sum (f := fun k : Fin 3 => ‖I (directionalFDeriv (coordinateDirection k) u x)‖^2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have hD := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hb.le)
  have hnn := inclusionEnergyDensity_nonneg I beta u x hb.le
  unfold inclusionEnergyDensity at *
  linarith

lemma abs_operator_pair_general (P : G →L[ℝ] F →L[ℝ] ℝ) (C : E →L[ℝ] F) (v : G) (u : E) :
    |P v (C u)| ≤ ‖P‖*‖C‖*(‖v‖*‖u‖) := by
  have hn : |P v (C u)| ≤ ‖P‖*‖v‖*‖C u‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm₂ P v (C u)
  calc _ ≤ ‖P‖*‖v‖*‖C u‖ := hn
       _ ≤ ‖P‖*‖v‖*(‖C‖*‖u‖) := mul_le_mul_of_nonneg_left (C.le_opNorm u) (by positivity)
       _ = _ := by ring

lemma abs_operator_mass_pair (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G)
    (C : E →L[ℝ] F) (u : E) : |P (I u) (C u)| ≤ ‖P‖*‖I‖*‖C‖*‖u‖^2 := by
  calc _ ≤ ‖P‖*‖C‖*(‖I u‖*‖u‖) := abs_operator_pair_general P C (I u) u
       _ ≤ ‖P‖*‖C‖*((‖I‖*‖u‖)*‖u‖) :=
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (I.le_opNorm u) (norm_nonneg u)) (by positivity)
       _ = _ := by ring

/-- Real coefficient bookkeeping that never asks for the high norm of a base derivative. -/
lemma reduced_first_point_bound
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (C D : E →L[ℝ] F)
    (u : E) (du : G) (mu dmu beta Q M eps energy : ℝ)
    (hmu : 0 ≤ mu) (hb : 1 ≤ beta) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (he : 0 ≤ energy) (hMass : ‖u‖^2 ≤ energy) (hMixed : ‖du‖*‖u‖ ≤ energy)
    (hC : ‖C‖ ≤ Q*eps/beta) (hD : ‖D‖ ≤ Q*eps) (hdmu : |dmu| ≤ M*mu) :
    |dmu*P (I u) (C u)+mu*P du (C u)+mu*P (I u) (D u)| ≤
      (‖P‖*Q*((M+1)*‖I‖+2)*eps)*(mu*energy) := by
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hi : beta⁻¹ ≤ 1 := (inv_le_one₀ hbpos).mpr hb
  have hMassInv : beta⁻¹*‖u‖^2 ≤ energy := by
    have h := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖u‖)
    exact (by simpa only [one_mul] using h : beta⁻¹*‖u‖^2 ≤ ‖u‖^2).trans hMass
  have hMixedInv : beta⁻¹*(‖du‖*‖u‖) ≤ energy := by
    have h := mul_le_mul_of_nonneg_right hi (mul_nonneg (norm_nonneg du) (norm_nonneg u))
    exact (by simpa only [one_mul] using h : beta⁻¹*(‖du‖*‖u‖) ≤ ‖du‖*‖u‖).trans hMixed
  have h1 : |dmu*P (I u) (C u)| ≤ (‖P‖*Q*M*‖I‖*eps)*(mu*energy) := by
    rw [abs_mul]
    calc _ ≤ (M*mu)*(‖P‖*‖I‖*‖C‖*‖u‖^2) :=
           mul_le_mul hdmu (abs_operator_mass_pair P I C u) (abs_nonneg _) (by positivity)
         _ ≤ (M*mu)*(‖P‖*‖I‖*(Q*eps/beta)*‖u‖^2) := by gcongr
         _ = (‖P‖*Q*M*‖I‖*eps*mu)*(beta⁻¹*‖u‖^2) := by rw [div_eq_mul_inv]; ring
         _ ≤ (‖P‖*Q*M*‖I‖*eps*mu)*energy := mul_le_mul_of_nonneg_left hMassInv (by positivity)
         _ = _ := by ring
  have h2 : |mu*P du (C u)| ≤ (‖P‖*Q*eps)*(mu*energy) := by
    rw [abs_mul,abs_of_nonneg hmu]
    calc _ ≤ mu*(‖P‖*‖C‖*(‖du‖*‖u‖)) := mul_le_mul_of_nonneg_left (abs_operator_pair_general P C du u) hmu
         _ ≤ mu*(‖P‖*(Q*eps/beta)*(‖du‖*‖u‖)) := by gcongr
         _ = (‖P‖*Q*eps*mu)*(beta⁻¹*(‖du‖*‖u‖)) := by rw [div_eq_mul_inv]; ring
         _ ≤ (‖P‖*Q*eps*mu)*energy := mul_le_mul_of_nonneg_left hMixedInv (by positivity)
         _ = _ := by ring
  have h3 : |mu*P (I u) (D u)| ≤ (‖P‖*Q*‖I‖*eps)*(mu*energy) := by
    rw [abs_mul,abs_of_nonneg hmu]
    calc _ ≤ mu*(‖P‖*‖I‖*‖D‖*‖u‖^2) := mul_le_mul_of_nonneg_left (abs_operator_mass_pair P I D u) hmu
         _ ≤ mu*(‖P‖*‖I‖*(Q*eps)*‖u‖^2) := by gcongr
         _ ≤ mu*(‖P‖*‖I‖*(Q*eps)*energy) := by gcongr
         _ = _ := by ring
  have ht := (abs_add_le (dmu*P (I u) (C u)+mu*P du (C u)) (mu*P (I u) (D u))).trans
    (add_le_add (abs_add_le (dmu*P (I u) (C u)) (mu*P du (C u))) le_rfl)
  have h0 : 0 ≤ ‖P‖*Q*eps*mu*energy := by positivity
  nlinarith only [ht,h1,h2,h3,h0]

def inclusionEnergy (I : E →L[ℝ] G) (mu beta : R3 → ℝ) (u : R3 → E) : ℝ :=
  ∫ x, mu x*inclusionEnergyDensity I (beta x) u x

lemma inclusionEnergy_integrable (I : E →L[ℝ] G) (mu beta : R3 → ℝ) (u : R3 → E)
    (K : Set R3) (hK : IsCompact K) (hm : Continuous mu) (hb : Continuous beta)
    (hb0 : ∀ x, beta x ≠ 0) (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0) :
    Integrable (fun x => mu x*inclusionEnergyDensity I (beta x) u x) := by
  have hd (i : Fin 3) : Continuous (fun x => ‖I (directionalFDeriv (coordinateDirection i) u x)‖^2) :=
    ((I.continuous.comp (contDiff_directionalFDeriv (coordinateDirection i) u hu).continuous).norm).pow 2
  have hcont : Continuous (fun x => mu x*inclusionEnergyDensity I (beta x) u x) :=
    hm.mul (((hb.inv₀ hb0).mul (continuous_finset_sum _ (fun i _ => hd i))).add
      (hb.mul (hu.continuous.norm.pow 2)))
  apply ActualHigherSIntegratedPairing.integrable_of_vanish _ hcont K hK
  intro x hx
  have hd0 (i : Fin 3) := directional_eq_zero_off u K hK.isClosed h0 (coordinateDirection i) x hx
  simp only [inclusionEnergyDensity,h0 x hx,hd0,map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero,mul_zero,add_zero]

lemma integrable_weighted_operator_pair_general
    (P : G →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (v : R3 → G) (u : R3 → E)
    (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : Continuous mu) (hv : Continuous v) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) :
    Integrable (fun x => mu x*P (v x) (C x (u x))) := by
  have h := compact_bilinear_integrable P (fun x => mu x • v x) _ (hm.smul hv)
    (contDiff_supported_operator_apply u C K hK.isClosed hu h0 hC).continuous
    (compact_supported_operator_apply u C K hK h0)
  convert h using 1
  funext x
  simp only [map_smul,smul_apply,smul_eq_mul]

/-- The zero-base commutator's first-base row is bounded using the included gradient only. -/
theorem weighted_first_operator_form_bound
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (mu beta : R3 → ℝ)
    (u : R3 → E) (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x)
    (Q M eps : ℝ) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hmu : ∀ x, 0 ≤ mu x) (hbeta : ∀ x ∈ K, 1 ≤ beta x) (i : Fin 3)
    (hC0 : ∀ x ∈ K, ‖C x‖ ≤ Q*eps/beta x)
    (hC1 : ∀ x ∈ K, ‖directionalFDeriv (coordinateDirection i) C x‖ ≤ Q*eps)
    (hdmu : ∀ x ∈ K, |directionalFDeriv (coordinateDirection i) mu x| ≤ M*mu x) :
    Integrable (fun x => mu x*P (I (u x)) (C x (directionalFDeriv (coordinateDirection i) u x))) ∧
    |∫ x, mu x*P (I (u x)) (C x (directionalFDeriv (coordinateDirection i) u x))| ≤
      (‖P‖*Q*((M+1)*‖I‖+2)*eps)*inclusionEnergy I mu beta u := by
  let X := coordinateDirection i
  let v : R3 → G := fun x => I (u x)
  let du := directionalFDeriv X u
  let dc := directionalFDeriv X C
  have hv : ContDiff ℝ ∞ v := contDiff_const.clm_apply hu
  have hdu := contDiff_directionalFDeriv X u hu
  have hd0 : ∀ x ∉ K, du x = 0 := fun x hx => directional_eq_zero_off u K hK.isClosed h0 X x hx
  have hdc : ∀ x ∈ K, ContDiffAt ℝ ∞ dc x :=
    fun x hx => contDiffAt_directional C x X (hC x hx)
  have hOrig := integrable_weighted_operator_pair_general P mu v du C K hK hm.continuous hv.continuous hdu hd0 hC
  refine ⟨hOrig,?_⟩
  rw [weighted_first_operator_green P I mu u C K hK hm hu h0 hC X,abs_neg]
  let R : R3 → ℝ := fun x => directionalFDeriv X mu x*P (I (u x)) (C x (u x))+
      mu x*P (I (du x)) (C x (u x))+mu x*P (I (u x)) (dc x (u x))
  have hRi : Integrable R :=
    ((integrable_weighted_operator_pair_general P (directionalFDeriv X mu) v u C K hK
      (contDiff_directionalFDeriv X mu hm).continuous hv.continuous hu h0 hC).add
    (integrable_weighted_operator_pair_general P mu (fun x => I (du x)) u C K hK hm.continuous
      (contDiff_const.clm_apply hdu).continuous hu h0 hC)).add
    (integrable_weighted_operator_pair_general P mu v u dc K hK hm.continuous hv.continuous hu h0 hdc)
  have hEi := inclusionEnergy_integrable I mu beta u K hK hm.continuous hbcont
    (fun x => (hbpos x).ne') hu h0
  let q : ℝ := ‖P‖*Q*((M+1)*‖I‖+2)*eps
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hPt (x : R3) : |R x| ≤ q*(mu x*inclusionEnergyDensity I (beta x) u x) := by
    by_cases hx : x ∈ K
    · exact reduced_first_point_bound P I (C x) (dc x) (u x) (I (du x))
        (mu x) (directionalFDeriv X mu x) (beta x) Q M eps (inclusionEnergyDensity I (beta x) u x)
        (hmu x) (hbeta x hx) hQ hM heps (inclusionEnergyDensity_nonneg I _ u x (hbpos x).le)
        (inclusion_energy_mass_le I _ u x (hbeta x hx))
        (inclusion_energy_mixed_le I _ u x (hbpos x) i) (hC0 x hx) (hC1 x hx) (hdmu x hx)
    · have hR0 : R x = 0 := by
        simp only [R,h0 x hx,hd0 x hx,map_zero,zero_apply,mul_zero,add_zero]
      rw [hR0,abs_zero]
      exact mul_nonneg hq (mul_nonneg (hmu x) (inclusionEnergyDensity_nonneg I _ u x (hbpos x).le))
  change |∫ x, R x| ≤ q*inclusionEnergy I mu beta u
  calc _ ≤ ∫ x, |R x| := abs_integral_le_integral_abs
       _ ≤ ∫ x, q*(mu x*inclusionEnergyDensity I (beta x) u x) :=
         integral_mono hRi.abs (hEi.const_mul q) hPt
       _ = _ := integral_const_mul q _

/-- Mass row in the same included-gradient/high-mass energy. -/
theorem weighted_mass_operator_form_bound
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (mu beta : R3 → ℝ)
    (u : R3 → E) (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : Continuous mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x)
    (Q eps : ℝ) (hQ : 0 ≤ Q) (heps : 0 ≤ eps)
    (hmu : ∀ x, 0 ≤ mu x) (hbeta : ∀ x ∈ K, 1 ≤ beta x)
    (hC0 : ∀ x ∈ K, ‖C x‖ ≤ Q*eps) :
    Integrable (fun x => mu x*P (I (u x)) (C x (u x))) ∧
    |∫ x, mu x*P (I (u x)) (C x (u x))| ≤ (‖P‖*‖I‖*Q*eps)*inclusionEnergy I mu beta u := by
  have hv : Continuous (fun x => I (u x)) := I.continuous.comp hu.continuous
  have hOrig := integrable_weighted_operator_pair_general P mu _ u C K hK hm hv hu h0 hC
  have hEi := inclusionEnergy_integrable I mu beta u K hK hm hbcont (fun x => (hbpos x).ne') hu h0
  let q : ℝ := ‖P‖*‖I‖*Q*eps
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hPt (x : R3) : |mu x*P (I (u x)) (C x (u x))| ≤
      q*(mu x*inclusionEnergyDensity I (beta x) u x) := by
    by_cases hx : x ∈ K
    · have hmux := hmu x
      rw [abs_mul,abs_of_nonneg hmux]
      calc _ ≤ mu x*(‖P‖*‖I‖*‖C x‖*‖u x‖^2) :=
             mul_le_mul_of_nonneg_left (abs_operator_mass_pair P I (C x) (u x)) hmux
           _ ≤ mu x*(‖P‖*‖I‖*(Q*eps)*‖u x‖^2) := by gcongr; exact hC0 x hx
           _ ≤ mu x*(‖P‖*‖I‖*(Q*eps)*inclusionEnergyDensity I (beta x) u x) := by
             gcongr
             exact inclusion_energy_mass_le I (beta x) u x (hbeta x hx)
           _ = _ := by dsimp [q]; ring
    · simp only [h0 x hx,map_zero,zero_apply,mul_zero,abs_zero]
      exact mul_nonneg hq (mul_nonneg (hmu x) (inclusionEnergyDensity_nonneg I _ u x (hbpos x).le))
  refine ⟨hOrig,?_⟩
  calc _ ≤ ∫ x, |mu x*P (I (u x)) (C x (u x))| := abs_integral_le_integral_abs
       _ ≤ ∫ x, q*(mu x*inclusionEnergyDensity I (beta x) u x) :=
         integral_mono hOrig.abs (hEi.const_mul q) hPt
       _ = _ := integral_const_mul q _

lemma scalar_zero_commutator_supported (a : ℝ) (Z : R3 → (E →L[ℝ] F)) (u : R3 → E)
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hZ : ∀ x ∈ K, ContDiffAt ℝ ∞ Z x) (X Y x : R3) :
    Z x (a • directionalFDeriv X (directionalFDeriv Y u) x)-
      a • directionalFDeriv X (directionalFDeriv Y (fun y => Z y (u y))) x =
      -(a • directionalFDeriv X (directionalFDeriv Y Z) x (u x))-
      a • directionalFDeriv Y Z x (directionalFDeriv X u x)-
      a • directionalFDeriv X Z x (directionalFDeriv Y u x) := by
  rw [directional_second_operator_apply_supported Z u K hK hu h0 hZ X Y x]
  simp only [map_smul,smul_add]
  module

def scalarZeroCoordinateCommutator (a : R3 → ℝ) (Z : R3 → (E →L[ℝ] F))
    (u : R3 → E) (i j : Fin 3) (x : R3) : F :=
  Z x (a x • directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) x)-
    a x • directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
      (fun y => Z y (u y))) x

/-- Full literal zero-base/scalar-principal row; no high norm of a base derivative is assumed. -/
theorem scalar_zero_coordinate_commutator_form_bound
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (mu beta : R3 → ℝ)
    (u : R3 → E) (a : R3 → ℝ) (Z : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0) (ha : ContDiff ℝ ∞ a)
    (hZ : ∀ x ∈ K, ContDiffAt ℝ ∞ Z x)
    (Q M eps : ℝ) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hmu : ∀ x, 0 ≤ mu x) (hbeta : ∀ x ∈ K, 1 ≤ beta x) (i j : Fin 3)
    (hdmu : ∀ k : Fin 3, ∀ x ∈ K,
      |directionalFDeriv (coordinateDirection k) mu x| ≤ M*mu x)
    (hCi : ∀ x ∈ K, ‖operatorDerivativeProduct (coordinateDirection j) a Z x‖ ≤ Q*eps/beta x ∧
      ‖directionalFDeriv (coordinateDirection i) (operatorDerivativeProduct (coordinateDirection j) a Z) x‖ ≤ Q*eps)
    (hCj : ∀ x ∈ K, ‖operatorDerivativeProduct (coordinateDirection i) a Z x‖ ≤ Q*eps/beta x ∧
      ‖directionalFDeriv (coordinateDirection j) (operatorDerivativeProduct (coordinateDirection i) a Z) x‖ ≤ Q*eps)
    (hD : ∀ x ∈ K, ‖secondOperatorDerivativeProduct (coordinateDirection i) (coordinateDirection j) a Z x‖ ≤ Q*eps) :
    Integrable (fun x => mu x*P (I (u x)) (scalarZeroCoordinateCommutator a Z u i j x)) ∧
    |∫ x, mu x*P (I (u x)) (scalarZeroCoordinateCommutator a Z u i j x)| ≤
      (3*‖P‖*Q*((M+1)*‖I‖+2)*eps)*inclusionEnergy I mu beta u := by
  let Ci := operatorDerivativeProduct (coordinateDirection j) a Z
  let Cj := operatorDerivativeProduct (coordinateDirection i) a Z
  let D := secondOperatorDerivativeProduct (coordinateDirection i) (coordinateDirection j) a Z
  have hgi : ∀ x ∈ K, ContDiffAt ℝ ∞ Ci x := fun x hx =>
    ha.contDiffAt.smul (contDiffAt_directional Z x (coordinateDirection j) (hZ x hx))
  have hgj : ∀ x ∈ K, ContDiffAt ℝ ∞ Cj x := fun x hx =>
    ha.contDiffAt.smul (contDiffAt_directional Z x (coordinateDirection i) (hZ x hx))
  have hgD : ∀ x ∈ K, ContDiffAt ℝ ∞ D x := fun x hx =>
    ha.contDiffAt.smul (contDiffAt_directional (directionalFDeriv (coordinateDirection j) Z)
      x (coordinateDirection i) (contDiffAt_directional Z x (coordinateDirection j) (hZ x hx)))
  have ri := weighted_first_operator_form_bound P I mu beta u Ci K hK hm hbcont hbpos hu h0 hgi
    Q M eps hQ hM heps hmu hbeta i (fun x hx => (hCi x hx).1) (fun x hx => (hCi x hx).2) (hdmu i)
  have rj := weighted_first_operator_form_bound P I mu beta u Cj K hK hm hbcont hbpos hu h0 hgj
    Q M eps hQ hM heps hmu hbeta j (fun x hx => (hCj x hx).1) (fun x hx => (hCj x hx).2) (hdmu j)
  have rD := weighted_mass_operator_form_bound P I mu beta u D K hK hm.continuous hbcont hbpos
    hu h0 hgD Q eps hQ heps hmu hbeta hD
  let A : R3 → ℝ := fun x => mu x*P (I (u x)) (Ci x (directionalFDeriv (coordinateDirection i) u x))
  let B : R3 → ℝ := fun x => mu x*P (I (u x)) (Cj x (directionalFDeriv (coordinateDirection j) u x))
  let C : R3 → ℝ := fun x => mu x*P (I (u x)) (D x (u x))
  have hEq : (fun x => mu x*P (I (u x)) (scalarZeroCoordinateCommutator a Z u i j x)) =
      fun x => -C x-A x-B x := by
    funext x
    rw [scalarZeroCoordinateCommutator,scalar_zero_commutator_supported (a x) Z u K hK.isClosed hu h0 hZ]
    simp only [A,B,C,Ci,Cj,D,operatorDerivativeProduct,secondOperatorDerivativeProduct,
      smul_apply,map_sub,map_neg,mul_sub,mul_neg]
  have hAi : Integrable A := ri.1
  have hBi : Integrable B := rj.1
  have hCi : Integrable C := rD.1
  have hAll : Integrable (fun x => -C x-A x-B x) := (hCi.neg.sub hAi).sub hBi
  have hI2 : (∫ x, -C x-A x-B x) = (∫ x, -C x-A x)-(∫ x, B x) := integral_sub (hCi.neg.sub hAi) hBi
  have hI1 : (∫ x, -C x-A x) = -(∫ x, C x)-(∫ x, A x) := by
    have h : (∫ x, -C x-A x) = (∫ x, -C x)-(∫ x, A x) := integral_sub hCi.neg hAi
    rw [integral_neg] at h
    exact h
  refine ⟨hEq.symm ▸ hAll,?_⟩
  rw [hEq,hI2,hI1]
  have hEn : 0 ≤ inclusionEnergy I mu beta u :=
    integral_nonneg (fun x => mul_nonneg (hmu x) (inclusionEnergyDensity_nonneg I _ u x (hbpos x).le))
  have hCbound : |∫ x, C x| ≤ (‖P‖*Q*((M+1)*‖I‖+2)*eps)*inclusionEnergy I mu beta u := by
    calc _ ≤ (‖P‖*‖I‖*Q*eps)*inclusionEnergy I mu beta u := rD.2
         _ = (‖P‖*Q*eps*inclusionEnergy I mu beta u)*‖I‖ := by ring
         _ ≤ (‖P‖*Q*eps*inclusionEnergy I mu beta u)*((M+1)*‖I‖+2) := by
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           nlinarith [mul_nonneg hM (norm_nonneg I)]
         _ = _ := by ring
  have hA : |∫ x, A x| ≤ (‖P‖*Q*((M+1)*‖I‖+2)*eps)*inclusionEnergy I mu beta u := ri.2
  have hB : |∫ x, B x| ≤ (‖P‖*Q*((M+1)*‖I‖+2)*eps)*inclusionEnergy I mu beta u := rj.2
  have ht1 : |-(∫ x, C x)-(∫ x, A x)| ≤ |∫ x, C x|+|∫ x, A x| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (-(∫ x, C x)) 0 (∫ x, A x)
  have ht2 : |-(∫ x, C x)-(∫ x, A x)-(∫ x, B x)| ≤
      |-(∫ x, C x)-(∫ x, A x)|+|∫ x, B x| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (-(∫ x, C x)-(∫ x, A x)) 0 (∫ x, B x)
  nlinarith only [ht1,ht2,hA,hB,hCbound]

/-- Joint positive coefficient factors for the zero-base commutator, with its true single radius gain. -/
def ZeroCommutatorCoefficientBudget (a : Fin 3 → Fin 3 → R3 → ℝ)
    (Z : R3 → (E →L[ℝ] F)) (x : R3) (eps r beta Q : ℝ) : Prop :=
  ∀ i j k m : Fin 3,
    ‖operatorDerivativeProduct (coordinateDirection k) (a i j) Z x‖ ≤ Q*eps*r/beta ∧
    ‖directionalFDeriv (coordinateDirection m) (operatorDerivativeProduct (coordinateDirection k) (a i j) Z) x‖ ≤ Q*eps*r ∧
    ‖secondOperatorDerivativeProduct (coordinateDirection i) (coordinateDirection j) (a i j) Z x‖ ≤ Q*eps*r

lemma zeroCommutatorCoefficientBudget_of_bounds
    (a : Fin 3 → Fin 3 → R3 → ℝ) (Z : R3 → (E →L[ℝ] F))
    (x : R3) (eps r beta A B : ℝ) (heps : 0 ≤ eps) (hr : 0 ≤ r) (hb : 0 < beta)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hZ : ContDiffAt ℝ ∞ Z x)
    (ha0 : ∀ i j, |a i j x| ≤ A*eps/beta^2)
    (ha1 : ∀ i j k, |directionalFDeriv (coordinateDirection k) (a i j) x| ≤ A*eps/beta)
    (hZ1 : ∀ k : Fin 3, ‖directionalFDeriv (coordinateDirection k) Z x‖ ≤ B*r*beta)
    (hZ2 : ∀ k m : Fin 3, ‖directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection k) Z) x‖ ≤ B*r*beta^2) :
    ZeroCommutatorCoefficientBudget a Z x eps r beta (2*A*B) := by
  have hnr : 0 ≤ A*B*eps*r := by positivity
  have hup (z : ℝ) (hz : z ≤ A*B*eps*r) : z ≤ (2*A*B)*eps*r := by nlinarith only [hz,hnr]
  have hupDiv (z : ℝ) (hz : z ≤ A*B*eps*r/beta) : z ≤ (2*A*B)*eps*r/beta := by
    have hn : 0 ≤ A*B*eps*r/beta := div_nonneg hnr hb.le
    have he : (2*A*B)*eps*r/beta = 2*(A*B*eps*r/beta) := by ring
    rw [he]
    linarith
  intro i j k m
  have hp := product_first_jet_budget (a i j) (directionalFDeriv (coordinateDirection k) Z)
    x (coordinateDirection m) (ha i j) (contDiffAt_directional Z x (coordinateDirection k) hZ)
    (A*eps/beta^2) (A*eps/beta) (B*r*beta) (B*r*beta^2)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (ha0 i j) (ha1 i j m) (hZ1 k) (hZ2 k m)
  refine ⟨?_,?_,?_⟩
  · apply hupDiv
    calc _ ≤ (A*eps/beta^2)*(B*r*beta) := hp.1
         _ = _ := by field_simp [hb.ne'] <;> ring
  · calc _ ≤ (A*eps/beta)*(B*r*beta)+(A*eps/beta^2)*(B*r*beta^2) := hp.2
         _ = _ := by field_simp [hb.ne'] <;> ring
  · apply hup
    calc
      _ = |a i j x| *‖directionalFDeriv (coordinateDirection i)
          (directionalFDeriv (coordinateDirection j) Z) x‖ := by
            rw [secondOperatorDerivativeProduct,norm_smul,Real.norm_eq_abs]
      _ ≤ (A*eps/beta^2)*(B*r*beta^2) := mul_le_mul (ha0 i j) (hZ2 j i) (norm_nonneg _) (by positivity)
      _ = _ := by field_simp [hb.ne'] <;> ring

lemma zeroCommutatorCoefficientBudget_radius_le_one
    (a : Fin 3 → Fin 3 → R3 → ℝ) (Z : R3 → (E →L[ℝ] F))
    (x : R3) (eps r beta Q : ℝ) (heps : 0 ≤ eps) (hQ : 0 ≤ Q)
    (hr1 : r ≤ 1) (hb : 0 ≤ beta) (hcap : ZeroCommutatorCoefficientBudget a Z x eps r beta Q) :
    ZeroCommutatorCoefficientBudget a Z x eps 1 beta Q := by
  have hc : Q*eps*r ≤ Q*eps := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 (mul_nonneg hQ heps)
  have hd := div_le_div_of_nonneg_right hc hb
  intro i j k m
  have h := hcap i j k m
  simp only [mul_one]
  exact ⟨h.1.trans hd,h.2.1.trans hc,h.2.2.trans hc⟩

def scalarZeroCoordinateCommutatorSum (a : Fin 3 → Fin 3 → R3 → ℝ)
    (Z : R3 → (E →L[ℝ] F)) (u : R3 → E) (x : R3) : F :=
  ∑ i : Fin 3, ∑ j : Fin 3, scalarZeroCoordinateCommutator (a i j) Z u i j x

/-- All nine literal zero-base commutators, in the exact high-mass/included-gradient energy. -/
theorem scalar_zero_coordinate_commutator_sum_form_bound
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (mu beta : R3 → ℝ)
    (u : R3 → E) (a : Fin 3 → Fin 3 → R3 → ℝ) (Z : R3 → (E →L[ℝ] F))
    (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hZ : ∀ x ∈ K, ContDiffAt ℝ ∞ Z x)
    (Q M eps : ℝ) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hmu : ∀ x, 0 ≤ mu x) (hbeta : ∀ x ∈ K, 1 ≤ beta x)
    (hdmu : ∀ k : Fin 3, ∀ x ∈ K,
      |directionalFDeriv (coordinateDirection k) mu x| ≤ M*mu x)
    (hcap : ∀ x ∈ K, ZeroCommutatorCoefficientBudget a Z x eps 1 (beta x) Q) :
    Integrable (fun x => mu x*P (I (u x)) (scalarZeroCoordinateCommutatorSum a Z u x)) ∧
    |∫ x, mu x*P (I (u x)) (scalarZeroCoordinateCommutatorSum a Z u x)| ≤
      (27*‖P‖*Q*((M+1)*‖I‖+2)*eps)*inclusionEnergy I mu beta u := by
  let row : Fin 3 → Fin 3 → R3 → ℝ := fun i j x =>
    mu x*P (I (u x)) (scalarZeroCoordinateCommutator (a i j) Z u i j x)
  have hRow (i j : Fin 3) : Integrable (row i j) ∧
      |∫ x, row i j x| ≤ (3*‖P‖*Q*((M+1)*‖I‖+2)*eps)*inclusionEnergy I mu beta u := by
    apply scalar_zero_coordinate_commutator_form_bound P I mu beta u (a i j) Z K hK hm hbcont
      hbpos hu h0 (ha i j) hZ Q M eps hQ hM heps hmu hbeta i j hdmu
    · intro x hx
      have h := hcap x hx i j j i
      simpa only [mul_one] using And.intro h.1 h.2.1
    · intro x hx
      have h := hcap x hx i j i j
      simpa only [mul_one] using And.intro h.1 h.2.1
    · intro x hx
      have h := hcap x hx i j 0 0
      simpa only [mul_one] using h.2.2
  have hEq : (fun x => mu x*P (I (u x)) (scalarZeroCoordinateCommutatorSum a Z u x)) =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3, row i j x := by
    funext x
    simp only [scalarZeroCoordinateCommutatorSum,map_sum,Finset.mul_sum,row]
  have hInt := ActualHigherSIntegratedPairing.integrable_sum2 row (fun i j => (hRow i j).1)
  refine ⟨hEq.symm ▸ hInt,?_⟩
  rw [hEq,ActualHigherSIntegratedPairing.integral_sum2 row (fun i j => (hRow i j).1)]
  let T : ℝ := (3*‖P‖*Q*((M+1)*‖I‖+2)*eps)*inclusionEnergy I mu beta u
  have hJ (i : Fin 3) : |∑ j : Fin 3, ∫ x, row i j x| ≤ 3*T :=
    ActualScalarPrincipalSelfFormBound.abs_sum_fin_three_le (fun j => ∫ x, row i j x) T (fun j => (hRow i j).2)
  have hI : |∑ i : Fin 3, ∑ j : Fin 3, ∫ x, row i j x| ≤ 3*(3*T) :=
    ActualScalarPrincipalSelfFormBound.abs_sum_fin_three_le (fun i => ∑ j : Fin 3, ∫ x, row i j x) (3*T) hJ
  calc _ ≤ 3*(3*T) := hI
       _ = _ := by dsimp [T]; ring
end Generic
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroScalarCommutatorForm
