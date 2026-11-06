import Calderon.ActualHigherSScalarCommutatorCoefficients
import Calderon.ActualScalarPrincipalSelfFormBound
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSScalarCommutatorForm
open PrincipalCommutator ActualScalarPrincipalAdjoint PerturbedDensityAdjoint ReferenceDensityBounds
  ActualHigherSScalarCommutatorCoefficients ActualScalarPrincipalSelfFormBound

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tsupport_subset_of_zero_off (u : R3 → E) (K : Set R3) (hK : IsClosed K)
    (h0 : ∀ x ∉ K, u x = 0) : tsupport u ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (h0 x hn)

lemma directional_eq_zero_off (u : R3 → E) (K : Set R3) (hK : IsClosed K)
    (h0 : ∀ x ∉ K, u x = 0) (X x : R3) (hx : x ∉ K) :
    directionalFDeriv X u x = 0 := by
  have ht : x ∉ tsupport u := fun h => hx (tsupport_subset_of_zero_off u K hK h0 h)
  simp only [directionalFDeriv,fderiv_of_notMem_tsupport ℝ ht,ContinuousLinearMap.zero_apply]

/-- Native coefficient germs only on the closed support suffice for the full supported section. -/
lemma contDiff_supported_operator_apply (u : R3 → E) (C : R3 → (E →L[ℝ] F))
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) :
    ContDiff ℝ ∞ (fun x => C x (u x)) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x ∈ K
  · exact (hC x hx).clm_apply hu.contDiffAt
  · have he : (fun y => C y (u y)) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      simp only [h0 y hy,map_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma compact_supported_operator_apply (u : R3 → E) (C : R3 → (E →L[ℝ] F))
    (K : Set R3) (hK : IsCompact K) (h0 : ∀ x ∉ K, u x = 0) :
    HasCompactSupport (fun x => C x (u x)) :=
  HasCompactSupport.intro hK (fun x hx => by simp only [h0 x hx,map_zero])

lemma directional_operator_apply_supported (u : R3 → E) (C : R3 → (E →L[ℝ] F))
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (X x : R3) :
    directionalFDeriv X (fun y => C y (u y)) x =
      (directionalFDeriv X C x) (u x)+C x (directionalFDeriv X u x) := by
  by_cases hx : x ∈ K
  · unfold directionalFDeriv
    rw [fderiv_clm_apply ((hC x hx).differentiableAt (by simp))
      (hu.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    exact add_comm _ _
  · rw [directional_eq_zero_off (fun y => C y (u y)) K hK
        (fun y hy => by simp only [h0 y hy,map_zero]) X x hx,
      h0 x hx,directional_eq_zero_off u K hK h0 X x hx,map_zero,map_zero,add_zero]

lemma compact_bilinear_integrable (P : E →L[ℝ] F →L[ℝ] ℝ)
    (u : R3 → E) (v : R3 → F) (hu : Continuous u) (hv : Continuous v)
    (hc : HasCompactSupport v) : Integrable (fun x => P (u x) (v x)) := by
  apply ((P.continuous.comp hu).clm_apply hv).integrable_of_hasCompactSupport
  apply hc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp only [hx,map_zero]

/-- One Green step, with the coefficient derivative and the actual density derivative retained. -/
theorem weighted_second_operator_green
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (X Y : R3) :
    (∫ x, mu x * P (u x) (C x (directionalFDeriv X (directionalFDeriv Y u) x))) =
      -(∫ x, (directionalFDeriv X mu x)*P (u x) (C x (directionalFDeriv Y u x))+
        mu x*P (directionalFDeriv X u x) (C x (directionalFDeriv Y u x))+
        mu x*P (u x) ((directionalFDeriv X C x) (directionalFDeriv Y u x))) := by
  let v : R3 → E := directionalFDeriv Y u
  let z : R3 → F := fun x => C x (v x)
  let f : R3 → E := fun x => mu x • u x
  have hv : ContDiff ℝ ∞ v := contDiff_directionalFDeriv Y u hu
  have hv0 : ∀ x ∉ K, v x = 0 := fun x hx => directional_eq_zero_off u K hK.isClosed h0 Y x hx
  have hz : ContDiff ℝ ∞ z := contDiff_supported_operator_apply v C K hK.isClosed hv hv0 hC
  have hzc : HasCompactSupport z := compact_supported_operator_apply v C K hK hv0
  have hf : ContDiff ℝ ∞ f := hm.smul hu
  have hfi : Integrable (fun x => P (directionalFDeriv X f x) (z x)) :=
    compact_bilinear_integrable P _ _ (contDiff_directionalFDeriv X f hf).continuous hz.continuous hzc
  have hzi : Integrable (fun x => P (f x) (directionalFDeriv X z x)) :=
    compact_bilinear_integrable P _ _ hf.continuous (contDiff_directionalFDeriv X z hz).continuous
      (hzc.fderiv_apply (𝕜 := ℝ) X)
  have hbase : Integrable (fun x => P (f x) (z x)) :=
    compact_bilinear_integrable P _ _ hf.continuous hz.continuous hzc
  have hg := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := P) (v := X) hfi hzi hbase
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hz.differentiable (by simp) x)
  have hzD (x : R3) : directionalFDeriv X z x =
      directionalFDeriv X C x (v x)+C x (directionalFDeriv X v x) :=
    directional_operator_apply_supported v C K hK.isClosed hv hv0 hC X x
  have hfD (x : R3) : directionalFDeriv X f x =
      directionalFDeriv X mu x • u x+mu x • directionalFDeriv X u x :=
    directional_smul_at mu u x X hm.contDiffAt hu.contDiffAt
  let A : R3 → ℝ := fun x => mu x*P (u x) (C x (directionalFDeriv X v x))
  let B : R3 → ℝ := fun x => mu x*P (u x) ((directionalFDeriv X C x) (v x))
  let D : R3 → ℝ := fun x => directionalFDeriv X mu x*P (u x) (C x (v x))+
      mu x*P (directionalFDeriv X u x) (C x (v x))
  have hAB : (fun x => P (f x) (directionalFDeriv X z x)) = fun x => A x+B x := by
    funext x
    rw [hzD x]
    simp only [f,A,B,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,map_add]
    ring
  have hD : (fun x => P (directionalFDeriv X f x) (z x)) = D := by
    funext x
    rw [hfD x]
    simp only [D,z,map_add,map_smul,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul]
  have hBC : ContDiff ℝ ∞ (fun x => (directionalFDeriv X C x) (v x)) :=
    contDiff_supported_operator_apply v _ K hK.isClosed hv hv0
      (fun x hx => contDiffAt_directional C x X (hC x hx))
  have hBi : Integrable B := by
    have hh := compact_bilinear_integrable P f _ hf.continuous hBC.continuous
      (compact_supported_operator_apply v _ K hK hv0)
    convert hh using 1
    funext x
    simp only [B,f,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
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

lemma abs_operator_pair_le (P : E →L[ℝ] F →L[ℝ] ℝ) (C : E →L[ℝ] F) (v w : E) :
    |P v (C w)| ≤ ‖P‖*‖C‖*(‖v‖*‖w‖) := by
  have hn : |P v (C w)| ≤ ‖P‖*‖v‖*‖C w‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm₂ P v (C w)
  calc _ ≤ ‖P‖*‖v‖*‖C w‖ := hn
       _ ≤ ‖P‖*‖v‖*(‖C‖*‖w‖) :=
         mul_le_mul_of_nonneg_left (C.le_opNorm w) (by positivity)
       _ = _ := by ring

lemma integrable_weighted_supported_operator_pair
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (v u : R3 → E)
    (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : Continuous mu) (hv : Continuous v) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) :
    Integrable (fun x => mu x*P (v x) (C x (u x))) := by
  have h := compact_bilinear_integrable P (fun x => mu x • v x) _ (hm.smul hv)
    (contDiff_supported_operator_apply u C K hK.isClosed hu h0 hC).continuous
    (compact_supported_operator_apply u C K hK h0)
  convert h using 1
  funext x
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]

/-- Pointwise real bookkeeping after one actual Green step. -/
lemma reduced_second_point_bound
    (P : E →L[ℝ] F →L[ℝ] ℝ) (C D : E →L[ℝ] F) (v vi vj : E)
    (mu dmu beta Q M eps energy : ℝ)
    (hmu : 0 ≤ mu) (hb : 1 ≤ beta) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (he : 0 ≤ energy) (hC : ‖C‖ ≤ Q*eps/beta) (hD : ‖D‖ ≤ Q*eps)
    (hdmu : |dmu| ≤ M*mu)
    (hmix : ‖v‖*‖vj‖ ≤ energy) (hgrad : beta⁻¹*(‖vi‖*‖vj‖) ≤ energy) :
    |dmu*P v (C vj)+mu*P vi (C vj)+mu*P v (D vj)| ≤
      (‖P‖*Q*(M+3)*eps)*(mu*energy) := by
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hbInv : beta⁻¹ ≤ 1 := (inv_le_one₀ hbpos).mpr hb
  have hmixInv : beta⁻¹*(‖v‖*‖vj‖) ≤ energy := by
    have h := mul_le_mul_of_nonneg_right hbInv (mul_nonneg (norm_nonneg v) (norm_nonneg vj))
    have ht : beta⁻¹*(‖v‖*‖vj‖) ≤ ‖v‖*‖vj‖ := by simpa only [one_mul] using h
    exact ht.trans hmix
  have h1 : |dmu*P v (C vj)| ≤ (‖P‖*Q*M*eps)*(mu*energy) := by
    rw [abs_mul]
    calc
      _ ≤ (M*mu)*(‖P‖*‖C‖*(‖v‖*‖vj‖)) :=
        mul_le_mul hdmu (abs_operator_pair_le P C v vj) (abs_nonneg _) (by positivity)
      _ ≤ (M*mu)*(‖P‖*(Q*eps/beta)*(‖v‖*‖vj‖)) := by gcongr
      _ = (‖P‖*Q*M*eps*mu)*(beta⁻¹*(‖v‖*‖vj‖)) := by rw [div_eq_mul_inv]; ring
      _ ≤ (‖P‖*Q*M*eps*mu)*energy := mul_le_mul_of_nonneg_left hmixInv (by positivity)
      _ = _ := by ring
  have h2 : |mu*P vi (C vj)| ≤ (‖P‖*Q*eps)*(mu*energy) := by
    rw [abs_mul,abs_of_nonneg hmu]
    calc
      _ ≤ mu*(‖P‖*‖C‖*(‖vi‖*‖vj‖)) :=
        mul_le_mul_of_nonneg_left (abs_operator_pair_le P C vi vj) hmu
      _ ≤ mu*(‖P‖*(Q*eps/beta)*(‖vi‖*‖vj‖)) := by gcongr
      _ = (‖P‖*Q*eps*mu)*(beta⁻¹*(‖vi‖*‖vj‖)) := by rw [div_eq_mul_inv]; ring
      _ ≤ (‖P‖*Q*eps*mu)*energy := mul_le_mul_of_nonneg_left hgrad (by positivity)
      _ = _ := by ring
  have h3 : |mu*P v (D vj)| ≤ (‖P‖*Q*eps)*(mu*energy) := by
    rw [abs_mul,abs_of_nonneg hmu]
    calc
      _ ≤ mu*(‖P‖*‖D‖*(‖v‖*‖vj‖)) :=
        mul_le_mul_of_nonneg_left (abs_operator_pair_le P D v vj) hmu
      _ ≤ mu*(‖P‖*(Q*eps)*(‖v‖*‖vj‖)) := by gcongr
      _ ≤ mu*(‖P‖*(Q*eps)*energy) := by gcongr
      _ = _ := by ring
  have ht := (abs_add_le (dmu*P v (C vj)+mu*P vi (C vj)) (mu*P v (D vj))).trans
    (add_le_add (abs_add_le (dmu*P v (C vj)) (mu*P vi (C vj))) le_rfl)
  have hremain : 0 ≤ ‖P‖*Q*eps*mu*energy := by positivity
  nlinarith only [ht,h1,h2,h3,hremain]
end Generic

section Energy
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma coordinate_mixed_norm_le (v : Fin 3 → R3) (u : R3 → E) (x : R3)
    (beta : ℝ) (hb : 0 < beta) (j : Fin 3) :
    ‖u x‖*‖directionalFDeriv (v j) u x‖ ≤ coordinateEnergyDensity v beta u x := by
  have hY := mul_nonneg (inv_nonneg.mpr hb.le)
    (sq_nonneg (beta*‖u x‖-‖directionalFDeriv (v j) u x‖))
  have he : beta⁻¹*(beta*‖u x‖-‖directionalFDeriv (v j) u x‖)^2 =
      beta*‖u x‖^2+beta⁻¹*‖directionalFDeriv (v j) u x‖^2-
        2*‖u x‖*‖directionalFDeriv (v j) u x‖ := by
    field_simp [hb.ne'] <;> ring
  rw [he] at hY
  have hd := mul_le_mul_of_nonneg_left (coordinate_gradient_square_le v u x j)
    (inv_nonneg.mpr hb.le)
  have hnn : 0 ≤ coordinateEnergyDensity v beta u x := coordinateEnergyDensity_nonneg v beta u x hb.le
  unfold coordinateEnergyDensity at *
  linarith

lemma coordinate_gradient_inv_le (v : Fin 3 → R3) (u : R3 → E) (x : R3)
    (beta : ℝ) (hb : 0 ≤ beta) (i j : Fin 3) :
    beta⁻¹*(‖directionalFDeriv (v i) u x‖*‖directionalFDeriv (v j) u x‖) ≤
      coordinateEnergyDensity v beta u x := by
  have h := mul_le_mul_of_nonneg_left (coordinate_gradient_pair_le v u x i j)
    (inv_nonneg.mpr hb)
  unfold coordinateEnergyDensity
  exact h.trans (le_add_of_nonneg_right (mul_nonneg hb (sq_nonneg _)))

/-- Signed second-base coefficient row controlled by the genuine coordinate half-energy. -/
theorem weighted_second_operator_form_bound
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu beta : R3 → ℝ) (u : R3 → E)
    (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x)
    (Q M eps : ℝ) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hmu : ∀ x, 0 ≤ mu x) (hbeta : ∀ x ∈ K, 1 ≤ beta x) (i j : Fin 3)
    (hC0 : ∀ x ∈ K, ‖C x‖ ≤ Q*eps/beta x)
    (hC1 : ∀ x ∈ K, ‖directionalFDeriv (coordinateDirection i) C x‖ ≤ Q*eps)
    (hdmu : ∀ x ∈ K, |directionalFDeriv (coordinateDirection i) mu x| ≤ M*mu x) :
    Integrable (fun x => mu x*P (u x)
      (C x (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) x))) ∧
    |∫ x, mu x*P (u x)
      (C x (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) x))| ≤
        (‖P‖*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u := by
  let X := coordinateDirection i
  let Y := coordinateDirection j
  let v := directionalFDeriv Y u
  let Cx := directionalFDeriv X C
  have hv : ContDiff ℝ ∞ v := contDiff_directionalFDeriv Y u hu
  have hv0 : ∀ x ∉ K, v x = 0 := fun x hx => directional_eq_zero_off u K hK.isClosed h0 Y x hx
  have hv2 : ContDiff ℝ ∞ (directionalFDeriv X v) := contDiff_directionalFDeriv X v hv
  have hv20 : ∀ x ∉ K, directionalFDeriv X v x = 0 :=
    fun x hx => directional_eq_zero_off v K hK.isClosed hv0 X x hx
  have hCx : ∀ x ∈ K, ContDiffAt ℝ ∞ Cx x :=
    fun x hx => contDiffAt_directional C x X (hC x hx)
  have hOrig := integrable_weighted_supported_operator_pair P mu u (directionalFDeriv X v)
    C K hK hm.continuous hu.continuous hv2 hv20 hC
  refine ⟨hOrig,?_⟩
  rw [weighted_second_operator_green P mu u C K hK hm hu h0 hC X Y,abs_neg]
  let R : R3 → ℝ := fun x => directionalFDeriv X mu x*P (u x) (C x (v x))+
      mu x*P (directionalFDeriv X u x) (C x (v x))+mu x*P (u x) (Cx x (v x))
  have hRi : Integrable R :=
    ((integrable_weighted_supported_operator_pair P (directionalFDeriv X mu) u v C K hK
      (contDiff_directionalFDeriv X mu hm).continuous hu.continuous hv hv0 hC).add
    (integrable_weighted_supported_operator_pair P mu (directionalFDeriv X u) v C K hK
      hm.continuous (contDiff_directionalFDeriv X u hu).continuous hv hv0 hC)).add
    (integrable_weighted_supported_operator_pair P mu u v Cx K hK hm.continuous hu.continuous hv hv0 hCx)
  have huc : HasCompactSupport u := HasCompactSupport.intro hK h0
  have hEi := coordinateEnergy_integrable coordinateDirection mu beta u hm.continuous hbcont hbpos hu huc
  change |∫ x, R x| ≤ _
  apply abs_integral_of_supported_energy_bound coordinateDirection mu beta u K R
    (‖P‖*Q*(M+3)*eps) hmu (fun x => (hbpos x).le) (by positivity) hRi hEi
  · intro x hx
    exact reduced_second_point_bound P (C x) (Cx x) (u x) (directionalFDeriv X u x) (v x)
      (mu x) (directionalFDeriv X mu x) (beta x) Q M eps
      (coordinateEnergyDensity coordinateDirection (beta x) u x)
      (hmu x) (hbeta x hx) hQ hM heps
      (coordinateEnergyDensity_nonneg _ _ _ _ (hbpos x).le) (hC0 x hx) (hC1 x hx) (hdmu x hx)
      (coordinate_mixed_norm_le coordinateDirection u x (beta x) (hbpos x) j)
      (coordinate_gradient_inv_le coordinateDirection u x (beta x) (hbpos x).le i j)
  · intro x hx
    have hu0 := h0 x hx
    have hdu0 := directional_eq_zero_off u K hK.isClosed h0 X x hx
    simp only [R,hu0,hdu0,map_zero,zero_apply,mul_zero,add_zero]

/-- First-base row uses the same genuine weighted coordinate energy, without integration by parts. -/
theorem weighted_first_operator_form_bound
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu beta : R3 → ℝ) (u : R3 → E)
    (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : Continuous mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x)
    (Q eps : ℝ) (hQ : 0 ≤ Q) (heps : 0 ≤ eps) (hmu : ∀ x, 0 ≤ mu x)
    (j : Fin 3) (hC0 : ∀ x ∈ K, ‖C x‖ ≤ Q*eps) :
    Integrable (fun x => mu x*P (u x) (C x (directionalFDeriv (coordinateDirection j) u x))) ∧
    |∫ x, mu x*P (u x) (C x (directionalFDeriv (coordinateDirection j) u x))| ≤
      (‖P‖*Q*eps)*coordinateEnergy coordinateDirection mu beta u := by
  have hdu : ContDiff ℝ ∞ (directionalFDeriv (coordinateDirection j) u) :=
    contDiff_directionalFDeriv _ u hu
  have hd0 : ∀ x ∉ K, directionalFDeriv (coordinateDirection j) u x = 0 :=
    fun x hx => directional_eq_zero_off u K hK.isClosed h0 _ x hx
  have hOrig := integrable_weighted_supported_operator_pair P mu u _ C K hK hm hu.continuous hdu hd0 hC
  have hc : HasCompactSupport u := HasCompactSupport.intro hK h0
  have hEi := coordinateEnergy_integrable coordinateDirection mu beta u hm hbcont hbpos hu hc
  refine ⟨hOrig,?_⟩
  apply abs_integral_of_supported_energy_bound coordinateDirection mu beta u K _
    (‖P‖*Q*eps) hmu (fun x => (hbpos x).le) (by positivity) hOrig hEi
  · intro x hx
    rw [abs_mul,abs_of_nonneg (hmu x)]
    calc
      _ ≤ mu x*(‖P‖*‖C x‖*(‖u x‖*‖directionalFDeriv (coordinateDirection j) u x‖)) :=
        mul_le_mul_of_nonneg_left (abs_operator_pair_le P (C x) (u x) _) (hmu x)
      _ ≤ mu x*(‖P‖*(Q*eps)*(‖u x‖*‖directionalFDeriv (coordinateDirection j) u x‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC0 x hx) (norm_nonneg P))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (hmu x)
      _ ≤ mu x*(‖P‖*(Q*eps)*coordinateEnergyDensity coordinateDirection (beta x) u x) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (coordinate_mixed_norm_le coordinateDirection u x (beta x) (hbpos x) j)
            (by positivity)) (hmu x)
      _ = _ := by ring
  · intro x hx
    simp only [h0 x hx,map_zero,zero_apply,mul_zero]
end Energy

section SupportedCancellation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The native local-germ version of the checked second operator Leibniz rule. -/
lemma directional_second_operator_apply_supported
    (C : R3 → (E →L[ℝ] F)) (u : R3 → E) (K : Set R3) (hK : IsClosed K)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (X Y x : R3) :
    directionalFDeriv X (directionalFDeriv Y (fun y => C y (u y))) x =
      directionalFDeriv X (directionalFDeriv Y C) x (u x)+
      directionalFDeriv Y C x (directionalFDeriv X u x)+
      directionalFDeriv X C x (directionalFDeriv Y u x)+
      C x (directionalFDeriv X (directionalFDeriv Y u) x) := by
  have hEq : directionalFDeriv Y (fun y => C y (u y)) =
      fun y => directionalFDeriv Y C y (u y)+C y (directionalFDeriv Y u y) :=
    funext (directional_operator_apply_supported u C K hK hu h0 hC Y)
  have hCY : ∀ y ∈ K, ContDiffAt ℝ ∞ (directionalFDeriv Y C) y :=
    fun y hy => contDiffAt_directional C y Y (hC y hy)
  have hdu := contDiff_directionalFDeriv Y u hu
  have hd0 : ∀ y ∉ K, directionalFDeriv Y u y = 0 :=
    fun y hy => directional_eq_zero_off u K hK h0 Y y hy
  have hA := contDiff_supported_operator_apply u (directionalFDeriv Y C) K hK hu h0 hCY
  have hB := contDiff_supported_operator_apply (directionalFDeriv Y u) C K hK hdu hd0 hC
  rw [hEq,directionalFDeriv_add X _ _ hA hB,
    directional_operator_apply_supported u (directionalFDeriv Y C) K hK hu h0 hCY X x,
    directional_operator_apply_supported (directionalFDeriv Y u) C K hK hdu hd0 hC X x]
  abel

/-- Preserve the checked scalar-principal cancellation when only native coefficient germs are available. -/
theorem scalar_principal_directional_commutator_supported
    (i j l : R3) (a : R3 → ℝ) (C : R3 → (E →L[ℝ] F)) (u : R3 → E)
    (K : Set R3) (hK : IsClosed K) (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (x : R3) :
    C x (directionalFDeriv l (fun y => a y • directionalFDeriv i (directionalFDeriv j u) y) x)-
      a x • directionalFDeriv i (directionalFDeriv j (fun y => C y (directionalFDeriv l u y))) x =
      (scalarDerivativeProduct l a C x) (directionalFDeriv i (directionalFDeriv j u) x)-
      (secondOperatorDerivativeProduct i j a C x) (directionalFDeriv l u x)-
      (operatorDerivativeProduct j a C x) (directionalFDeriv i (directionalFDeriv l u) x)-
      (operatorDerivativeProduct i a C x) (directionalFDeriv j (directionalFDeriv l u) x) := by
  have hdu := contDiff_directionalFDeriv l u hu
  have hd0 : ∀ y ∉ K, directionalFDeriv l u y = 0 :=
    fun y hy => directional_eq_zero_off u K hK h0 l y hy
  rw [directionalFDeriv_smul l a _ ha
    (contDiff_directionalFDeriv i _ (contDiff_directionalFDeriv j u hu)),
    directional_second_operator_apply_supported C (directionalFDeriv l u) K hK hdu hd0 hC i j x,
    directionalFDeriv_third_commute i j l u hu]
  simp only [scalarDerivativeProduct,operatorDerivativeProduct,secondOperatorDerivativeProduct,
    map_add,map_smul,smul_add,ContinuousLinearMap.smul_apply]
  module
end SupportedCancellation

section FullRow
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Literal composed scalar-principal / first-coordinate operator commutator. -/
def scalarFirstCoordinateCommutator
    (a : R3 → ℝ) (b : R3 → (E →L[ℝ] F)) (u : R3 → E) (i j l : Fin 3) (x : R3) : F :=
  b x (directionalFDeriv (coordinateDirection l)
    (fun y => a y • directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) y) x)-
  a x • directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
    (fun y => b y (directionalFDeriv (coordinateDirection l) u y))) x

/-- All four surviving rows, with their true derivative pairs and signs, in the original composed form. -/
theorem scalar_first_coordinate_commutator_form_bound
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu beta : R3 → ℝ) (u : R3 → E)
    (a : R3 → ℝ) (b : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (ha : ContDiff ℝ ∞ a) (hb : ∀ x ∈ K, ContDiffAt ℝ ∞ b x)
    (Q M eps : ℝ) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hmu : ∀ x, 0 ≤ mu x) (hbeta : ∀ x ∈ K, 1 ≤ beta x) (i j l : Fin 3)
    (hdmu : ∀ k : Fin 3, ∀ x ∈ K,
      |directionalFDeriv (coordinateDirection k) mu x| ≤ M*mu x)
    (hC0 : ∀ x ∈ K,
      ‖scalarDerivativeProduct (coordinateDirection l) a b x‖ ≤ Q*eps/beta x ∧
      ‖directionalFDeriv (coordinateDirection i) (scalarDerivativeProduct (coordinateDirection l) a b) x‖ ≤ Q*eps)
    (hC1 : ∀ x ∈ K,
      ‖operatorDerivativeProduct (coordinateDirection j) a b x‖ ≤ Q*eps/beta x ∧
      ‖directionalFDeriv (coordinateDirection i) (operatorDerivativeProduct (coordinateDirection j) a b) x‖ ≤ Q*eps)
    (hC2 : ∀ x ∈ K,
      ‖operatorDerivativeProduct (coordinateDirection i) a b x‖ ≤ Q*eps/beta x ∧
      ‖directionalFDeriv (coordinateDirection j) (operatorDerivativeProduct (coordinateDirection i) a b) x‖ ≤ Q*eps)
    (hCF : ∀ x ∈ K,
      ‖secondOperatorDerivativeProduct (coordinateDirection i) (coordinateDirection j) a b x‖ ≤ Q*eps) :
    Integrable (fun x => mu x*P (u x) (scalarFirstCoordinateCommutator a b u i j l x)) ∧
    |∫ x, mu x*P (u x) (scalarFirstCoordinateCommutator a b u i j l x)| ≤
      (4*‖P‖*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u := by
  let C0 := scalarDerivativeProduct (coordinateDirection l) a b
  let C1 := operatorDerivativeProduct (coordinateDirection j) a b
  let C2 := operatorDerivativeProduct (coordinateDirection i) a b
  let CF := secondOperatorDerivativeProduct (coordinateDirection i) (coordinateDirection j) a b
  have hg0 : ∀ x ∈ K, ContDiffAt ℝ ∞ C0 x := fun x hx =>
    (contDiff_directionalFDeriv (coordinateDirection l) a ha).contDiffAt.smul (hb x hx)
  have hg1 : ∀ x ∈ K, ContDiffAt ℝ ∞ C1 x := fun x hx =>
    ha.contDiffAt.smul (contDiffAt_directional b x (coordinateDirection j) (hb x hx))
  have hg2 : ∀ x ∈ K, ContDiffAt ℝ ∞ C2 x := fun x hx =>
    ha.contDiffAt.smul (contDiffAt_directional b x (coordinateDirection i) (hb x hx))
  have hgF : ∀ x ∈ K, ContDiffAt ℝ ∞ CF x := fun x hx =>
    ha.contDiffAt.smul (contDiffAt_directional (directionalFDeriv (coordinateDirection j) b)
      x (coordinateDirection i) (contDiffAt_directional b x (coordinateDirection j) (hb x hx)))
  have r0 := weighted_second_operator_form_bound P mu beta u C0 K hK hm hbcont hbpos hu h0 hg0
    Q M eps hQ hM heps hmu hbeta i j (fun x hx => (hC0 x hx).1)
    (fun x hx => (hC0 x hx).2) (hdmu i)
  have r1 := weighted_second_operator_form_bound P mu beta u C1 K hK hm hbcont hbpos hu h0 hg1
    Q M eps hQ hM heps hmu hbeta i l (fun x hx => (hC1 x hx).1)
    (fun x hx => (hC1 x hx).2) (hdmu i)
  have r2 := weighted_second_operator_form_bound P mu beta u C2 K hK hm hbcont hbpos hu h0 hg2
    Q M eps hQ hM heps hmu hbeta j l (fun x hx => (hC2 x hx).1)
    (fun x hx => (hC2 x hx).2) (hdmu j)
  have rF := weighted_first_operator_form_bound P mu beta u CF K hK hm.continuous hbcont hbpos
    hu h0 hgF Q eps hQ heps hmu l hCF
  let A : R3 → ℝ := fun x => mu x*P (u x)
    (C0 x (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) x))
  let B : R3 → ℝ := fun x => mu x*P (u x)
    (C1 x (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection l) u) x))
  let C : R3 → ℝ := fun x => mu x*P (u x)
    (C2 x (directionalFDeriv (coordinateDirection j) (directionalFDeriv (coordinateDirection l) u) x))
  let D : R3 → ℝ := fun x => mu x*P (u x) (CF x (directionalFDeriv (coordinateDirection l) u x))
  have heq : (fun x => mu x*P (u x) (scalarFirstCoordinateCommutator a b u i j l x)) =
      fun x => A x-D x-B x-C x := by
    funext x
    have hc := scalar_principal_directional_commutator_supported
      (coordinateDirection i) (coordinateDirection j) (coordinateDirection l) a b u K hK.isClosed ha hu h0 hb x
    rw [scalarFirstCoordinateCommutator,hc]
    simp only [A,B,C,D,C0,C1,C2,CF,map_sub,mul_sub]
  have hAi : Integrable A := r0.1
  have hBi : Integrable B := r1.1
  have hCi : Integrable C := r2.1
  have hDi : Integrable D := rF.1
  have hInt : Integrable (fun x => A x-D x-B x-C x) := ((hAi.sub hDi).sub hBi).sub hCi
  refine ⟨heq.symm ▸ hInt,?_⟩
  have hI3 : (∫ x, A x-D x-B x-C x) = (∫ x, A x-D x-B x)-(∫ x, C x) := by
    exact integral_sub ((hAi.sub hDi).sub hBi) hCi
  have hI2 : (∫ x, A x-D x-B x) = (∫ x, A x-D x)-(∫ x, B x) := by
    exact integral_sub (hAi.sub hDi) hBi
  have hI1 : (∫ x, A x-D x) = (∫ x, A x)-(∫ x, D x) := integral_sub hAi hDi
  rw [heq,hI3,hI2,hI1]
  have hEn : 0 ≤ coordinateEnergy coordinateDirection mu beta u :=
    coordinateEnergy_nonneg coordinateDirection mu beta u hmu (fun x => (hbpos x).le)
  have hFB : |∫ x, D x| ≤ (‖P‖*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u := by
    calc _ ≤ (‖P‖*Q*eps)*coordinateEnergy coordinateDirection mu beta u := rF.2
         _ ≤ _ := by
           have h : 0 ≤ ‖P‖*Q*eps*coordinateEnergy coordinateDirection mu beta u := by positivity
           nlinarith only [h,mul_nonneg hM h]
  have ht1 : |(∫ x, A x)-(∫ x, D x)| ≤ |∫ x, A x|+|∫ x, D x| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (∫ x, A x) 0 (∫ x, D x)
  have ht2 : |(∫ x, A x)-(∫ x, D x)-(∫ x, B x)| ≤
      |(∫ x, A x)-(∫ x, D x)|+|∫ x, B x| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le ((∫ x, A x)-(∫ x, D x)) 0 (∫ x, B x)
  have ht3 : |(∫ x, A x)-(∫ x, D x)-(∫ x, B x)-(∫ x, C x)| ≤
      |(∫ x, A x)-(∫ x, D x)-(∫ x, B x)|+|∫ x, C x| := by
    simpa only [sub_zero,zero_sub,abs_neg] using
      abs_sub_le ((∫ x, A x)-(∫ x, D x)-(∫ x, B x)) 0 (∫ x, C x)
  have hA : |∫ x, A x| ≤ (‖P‖*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u := r0.2
  have hB : |∫ x, B x| ≤ (‖P‖*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u := r1.2
  have hC : |∫ x, C x| ≤ (‖P‖*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u := r2.2
  nlinarith only [ht1,ht2,ht3,hA,hB,hC,hFB]
end FullRow

section SumForm
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def scalarFirstCoordinateCommutatorSum
    (a : Fin 3 → Fin 3 → R3 → ℝ) (b : Fin 3 → R3 → (E →L[ℝ] F))
    (u : R3 → E) (x : R3) : F :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, scalarFirstCoordinateCommutator (a i j) (b l) u i j l x

lemma coordinateCommutatorCoefficientBudget_radius_le_one
    (a : Fin 3 → Fin 3 → R3 → ℝ) (b : Fin 3 → R3 → (E →L[ℝ] F))
    (x : R3) (eps r beta Q : ℝ) (heps : 0 ≤ eps) (hQ : 0 ≤ Q)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hb : 0 ≤ beta)
    (hcap : CoordinateCommutatorCoefficientBudget a b x eps r beta Q) :
    CoordinateCommutatorCoefficientBudget a b x eps 1 beta Q := by
  have hr2 : r^2 ≤ 1 := by nlinarith
  have hc : Q*eps*r^2 ≤ Q*eps := by
    have h := mul_le_mul_of_nonneg_left hr2 (mul_nonneg hQ heps)
    simpa only [mul_one] using h
  have hcd : Q*eps*r^2/beta ≤ Q*eps/beta := div_le_div_of_nonneg_right hc hb
  intro i j l k m
  have h := hcap i j l k m
  simp only [one_pow,mul_one]
  exact ⟨h.1.trans hcd,h.2.1.trans hc,h.2.2.1.trans hcd,h.2.2.2.1.trans hc,h.2.2.2.2.trans hc⟩

/-- Complete coordinate sum of the literal composed commutator, with a constant independent of angular size. -/
theorem scalar_first_coordinate_commutator_sum_form_bound
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu beta : R3 → ℝ) (u : R3 → E)
    (a : Fin 3 → Fin 3 → R3 → ℝ) (b : Fin 3 → R3 → (E →L[ℝ] F))
    (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hb : ∀ l, ∀ x ∈ K, ContDiffAt ℝ ∞ (b l) x)
    (Q M eps : ℝ) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hmu : ∀ x, 0 ≤ mu x) (hbeta : ∀ x ∈ K, 1 ≤ beta x)
    (hdmu : ∀ k : Fin 3, ∀ x ∈ K,
      |directionalFDeriv (coordinateDirection k) mu x| ≤ M*mu x)
    (hcap : ∀ x ∈ K, CoordinateCommutatorCoefficientBudget a b x eps 1 (beta x) Q) :
    Integrable (fun x => mu x*P (u x) (scalarFirstCoordinateCommutatorSum a b u x)) ∧
    |∫ x, mu x*P (u x) (scalarFirstCoordinateCommutatorSum a b u x)| ≤
      (108*‖P‖*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u := by
  let row : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ := fun i j l x =>
    mu x*P (u x) (scalarFirstCoordinateCommutator (a i j) (b l) u i j l x)
  have hRow (i j l : Fin 3) : Integrable (row i j l) ∧
      |∫ x, row i j l x| ≤ (4*‖P‖*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u := by
    apply scalar_first_coordinate_commutator_form_bound P mu beta u (a i j) (b l) K hK
      hm hbcont hbpos hu h0 (ha i j) (hb l) Q M eps hQ hM heps hmu hbeta i j l hdmu
    · intro x hx
      have h := hcap x hx i j l j i
      simpa only [one_pow,mul_one] using And.intro h.1 h.2.1
    · intro x hx
      have h := hcap x hx i j l j i
      simpa only [one_pow,mul_one] using And.intro h.2.2.1 h.2.2.2.1
    · intro x hx
      have h := hcap x hx i j l i j
      simpa only [one_pow,mul_one] using And.intro h.2.2.1 h.2.2.2.1
    · intro x hx
      have h := hcap x hx i j l 0 0
      simpa only [one_pow,mul_one] using h.2.2.2.2
  have heq : (fun x => mu x*P (u x) (scalarFirstCoordinateCommutatorSum a b u x)) =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, row i j l x := by
    funext x
    simp only [scalarFirstCoordinateCommutatorSum,map_sum,Finset.mul_sum,row]
  have hInt : Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, row i j l x) :=
    ActualHigherSIntegratedPairing.integrable_sum3 row (fun i j l => (hRow i j l).1)
  refine ⟨heq.symm ▸ hInt,?_⟩
  rw [heq,ActualHigherSIntegratedPairing.integral_sum3 row (fun i j l => (hRow i j l).1)]
  let T : ℝ := (4*‖P‖*Q*(M+3)*eps)*coordinateEnergy coordinateDirection mu beta u
  have hL (i j : Fin 3) : |∑ l : Fin 3, ∫ x, row i j l x| ≤ 3*T :=
    abs_sum_fin_three_le (fun l => ∫ x, row i j l x) T (fun l => (hRow i j l).2)
  have hJ (i : Fin 3) : |∑ j : Fin 3, ∑ l : Fin 3, ∫ x, row i j l x| ≤ 3*(3*T) :=
    abs_sum_fin_three_le (fun j => ∑ l : Fin 3, ∫ x, row i j l x) (3*T) (hL i)
  have hI : |∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, ∫ x, row i j l x| ≤ 3*(3*(3*T)) :=
    abs_sum_fin_three_le (fun i => ∑ j : Fin 3, ∑ l : Fin 3, ∫ x, row i j l x) (3*(3*T)) hJ
  calc _ ≤ 3*(3*(3*T)) := hI
       _ = _ := by dsimp [T]; ring
end SumForm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSScalarCommutatorForm
