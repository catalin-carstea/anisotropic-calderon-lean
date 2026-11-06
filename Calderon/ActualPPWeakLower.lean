import Calderon.ActualHigherSScalarCommutatorForm
import Calderon.ActualHigherSCoefficientExtraction

/-! This supplies weighted coordinate weak IBP, true-neighborhood differentiation
of a low pivot and the two-factor transpose used to balance the remainder.
It is NOT the actual same-packet P/P theorem: original data must discharge
all structural hypotheses, actual caps, finite sums and leading matching. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPWeakLower
open PrincipalCommutator ActualScalarPrincipalAdjoint PerturbedDensityAdjoint
  ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ActualHigherSCoefficientExtraction ActualHigherSScalarCommutatorCoefficients

section WeakGreen
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Reverse the one-Green-step identity while retaining both lower
coefficient/density derivatives. All compact-support integrability is derived. -/
theorem weighted_first_operator_green
    (Q : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (U : R3 → E)
    (C : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hmu : ContDiff ℝ ∞ mu) (hU : ContDiff ℝ ∞ U)
    (h0 : ∀ x ∉ K, U x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x)
    (X Y : R3) :
    (∫ x, mu x*Q (directionalFDeriv X U x) (C x (directionalFDeriv Y U x))) =
    -(∫ x, mu x*Q (U x) (C x (directionalFDeriv X (directionalFDeriv Y U) x)))-
    (∫ x, directionalFDeriv X mu x*Q (U x) (C x (directionalFDeriv Y U x))+
      mu x*Q (U x) (directionalFDeriv X C x (directionalFDeriv Y U x))) := by
  let v := directionalFDeriv Y U
  let A : R3 → ℝ := fun x => mu x*Q (U x) (C x (directionalFDeriv X v x))
  let B : R3 → ℝ := fun x => mu x*Q (directionalFDeriv X U x) (C x (v x))
  let D : R3 → ℝ := fun x => directionalFDeriv X mu x*Q (U x) (C x (v x))
  let H : R3 → ℝ := fun x => mu x*Q (U x) (directionalFDeriv X C x (v x))
  have hv : ContDiff ℝ ∞ v := contDiff_directionalFDeriv Y U hU
  have hv0 : ∀ x ∉ K, v x = 0 := fun x hx =>
    directional_eq_zero_off U K hK.isClosed h0 Y x hx
  have hBi : Integrable B := integrable_weighted_supported_operator_pair
    Q mu (directionalFDeriv X U) v C K hK hmu.continuous
    (contDiff_directionalFDeriv X U hU).continuous hv hv0 hC
  have hDi : Integrable D := integrable_weighted_supported_operator_pair
    Q (directionalFDeriv X mu) U v C K hK
    (contDiff_directionalFDeriv X mu hmu).continuous hU.continuous hv hv0 hC
  have hHi : Integrable H := integrable_weighted_supported_operator_pair
    Q mu U v (directionalFDeriv X C) K hK hmu.continuous hU.continuous hv hv0
    (fun x hx => contDiffAt_directional C x X (hC x hx))
  have hg := weighted_second_operator_green Q mu U C K hK hmu hU h0 hC X Y
  change (∫ x, A x) = -(∫ x, D x+B x+H x) at hg
  have heq : (fun x => D x+B x+H x) = (fun x => B x+(D x+H x)) := by
    funext x
    ring
  rw [heq] at hg
  have hsplit : (∫ x, B x+(D x+H x))=(∫ x,B x)+(∫ x,D x+H x) :=
    integral_add (f := B) (g := fun x => D x+H x) hBi (hDi.add hHi)
  rw [hsplit] at hg
  change (∫ x, B x) = -(∫ x, A x)-(∫ x, D x+H x)
  linarith

/-- Complete structural ordered P/P weak row. The two mixed second derivatives
are displayed separately; actual smooth-input commutation is a later explicit step. -/
theorem first_first_weak_row
    (Q : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (U : R3 → E)
    (C1 C2 : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hmu : ContDiff ℝ ∞ mu) (hU : ContDiff ℝ ∞ U)
    (h0 : ∀ x ∉ K, U x = 0)
    (hC1 : ∀ x ∈ K, ContDiffAt ℝ ∞ C1 x)
    (hC2 : ∀ x ∈ K, ContDiffAt ℝ ∞ C2 x) (X Y : R3) :
    (∫ x, mu x*(-Q (directionalFDeriv X U x) (C1 x (directionalFDeriv Y U x))+
      Q (directionalFDeriv Y U x) (C2 x (directionalFDeriv X U x)))) =
    (∫ x, mu x*(Q (U x) (C1 x (directionalFDeriv X (directionalFDeriv Y U) x))-
      Q (U x) (C2 x (directionalFDeriv Y (directionalFDeriv X U) x))))+
    (∫ x, directionalFDeriv X mu x*Q (U x) (C1 x (directionalFDeriv Y U x))+
      mu x*Q (U x) (directionalFDeriv X C1 x (directionalFDeriv Y U x))-
      directionalFDeriv Y mu x*Q (U x) (C2 x (directionalFDeriv X U x))-
      mu x*Q (U x) (directionalFDeriv Y C2 x (directionalFDeriv X U x))) := by
  let b1 : R3 → ℝ := fun x => mu x*Q (directionalFDeriv X U x) (C1 x (directionalFDeriv Y U x))
  let b2 : R3 → ℝ := fun x => mu x*Q (directionalFDeriv Y U x) (C2 x (directionalFDeriv X U x))
  let a1 : R3 → ℝ := fun x => mu x*Q (U x) (C1 x (directionalFDeriv X (directionalFDeriv Y U) x))
  let a2 : R3 → ℝ := fun x => mu x*Q (U x) (C2 x (directionalFDeriv Y (directionalFDeriv X U) x))
  let d1 : R3 → ℝ := fun x => directionalFDeriv X mu x*Q (U x) (C1 x (directionalFDeriv Y U x))
  let d2 : R3 → ℝ := fun x => directionalFDeriv Y mu x*Q (U x) (C2 x (directionalFDeriv X U x))
  let e1 : R3 → ℝ := fun x => mu x*Q (U x) (directionalFDeriv X C1 x (directionalFDeriv Y U x))
  let e2 : R3 → ℝ := fun x => mu x*Q (U x) (directionalFDeriv Y C2 x (directionalFDeriv X U x))
  have hDX := contDiff_directionalFDeriv X U hU
  have hDY := contDiff_directionalFDeriv Y U hU
  have hX0 : ∀ x ∉ K, directionalFDeriv X U x = 0 :=
    fun x hx => directional_eq_zero_off U K hK.isClosed h0 X x hx
  have hY0 : ∀ x ∉ K, directionalFDeriv Y U x = 0 :=
    fun x hx => directional_eq_zero_off U K hK.isClosed h0 Y x hx
  have hXY0 : ∀ x ∉ K, directionalFDeriv X (directionalFDeriv Y U) x = 0 :=
    fun x hx => directional_eq_zero_off _ K hK.isClosed hY0 X x hx
  have hYX0 : ∀ x ∉ K, directionalFDeriv Y (directionalFDeriv X U) x = 0 :=
    fun x hx => directional_eq_zero_off _ K hK.isClosed hX0 Y x hx
  have hb1 : Integrable b1 := integrable_weighted_supported_operator_pair Q mu _ _ C1 K hK
    hmu.continuous hDX.continuous hDY hY0 hC1
  have hb2 : Integrable b2 := integrable_weighted_supported_operator_pair Q mu _ _ C2 K hK
    hmu.continuous hDY.continuous hDX hX0 hC2
  have ha1 : Integrable a1 := integrable_weighted_supported_operator_pair Q mu U _ C1 K hK
    hmu.continuous hU.continuous (contDiff_directionalFDeriv X _ hDY) hXY0 hC1
  have ha2 : Integrable a2 := integrable_weighted_supported_operator_pair Q mu U _ C2 K hK
    hmu.continuous hU.continuous (contDiff_directionalFDeriv Y _ hDX) hYX0 hC2
  have hd1 : Integrable d1 := integrable_weighted_supported_operator_pair Q _ U _ C1 K hK
    (contDiff_directionalFDeriv X mu hmu).continuous hU.continuous hDY hY0 hC1
  have hd2 : Integrable d2 := integrable_weighted_supported_operator_pair Q _ U _ C2 K hK
    (contDiff_directionalFDeriv Y mu hmu).continuous hU.continuous hDX hX0 hC2
  have he1 : Integrable e1 := integrable_weighted_supported_operator_pair Q mu U _ _ K hK
    hmu.continuous hU.continuous hDY hY0
    (fun x hx => contDiffAt_directional C1 x X (hC1 x hx))
  have he2 : Integrable e2 := integrable_weighted_supported_operator_pair Q mu U _ _ K hK
    hmu.continuous hU.continuous hDX hX0
    (fun x hx => contDiffAt_directional C2 x Y (hC2 x hx))
  have hg1 := weighted_first_operator_green Q mu U C1 K hK hmu hU h0 hC1 X Y
  have hg2 := weighted_first_operator_green Q mu U C2 K hK hmu hU h0 hC2 Y X
  change (∫ x, b1 x) = -(∫ x, a1 x)-(∫ x, d1 x+e1 x) at hg1
  change (∫ x, b2 x) = -(∫ x, a2 x)-(∫ x, d2 x+e2 x) at hg2
  rw [integral_add hd1 he1] at hg1
  rw [integral_add hd2 he2] at hg2
  have hleft : (fun x => mu x*(-Q (directionalFDeriv X U x) (C1 x (directionalFDeriv Y U x))+
      Q (directionalFDeriv Y U x) (C2 x (directionalFDeriv X U x)))) =
      (fun x => -b1 x+b2 x) := by funext x; dsimp [b1,b2]; ring
  have hlead : (fun x => mu x*(Q (U x) (C1 x (directionalFDeriv X (directionalFDeriv Y U) x))-
      Q (U x) (C2 x (directionalFDeriv Y (directionalFDeriv X U) x)))) =
      (fun x => a1 x-a2 x) := by funext x; dsimp [a1,a2]; ring
  rw [hleft, hlead]
  change (∫ x, -b1 x+b2 x) = (∫ x, a1 x-a2 x)+(∫ x, d1 x+e1 x-d2 x-e2 x)
  rw [integral_add (f := fun x => -b1 x) (g := b2) hb1.neg hb2, integral_neg,
    integral_sub (f := a1) (g := a2) ha1 ha2,
    integral_sub (f := fun x => d1 x+e1 x-d2 x) (g := e2) ((hd1.add he1).sub hd2) he2,
    integral_sub (f := fun x => d1 x+e1 x) (g := d2) (hd1.add he1) hd2,
    integral_add (f := d1) (g := e1) hd1 he1]
  linarith
end WeakGreen

section LocalPivot
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- Point derivative of a continuous bilinear pairing, using the CLM
application derivative boundary; global smoothness is not required. -/
lemma directional_bilinear_at (P : H →L[ℝ] N →L[ℝ] ℝ)
    (v : R3 → H) (w : R3 → N) (x X : R3)
    (hv : DifferentiableAt ℝ v x) (hw : DifferentiableAt ℝ w x) :
    directionalFDeriv X (fun y => P (v y) (w y)) x =
      P (v x) (directionalFDeriv X w x)+P (directionalFDeriv X v x) (w x) := by
  have hPv : DifferentiableAt ℝ (fun y => P (v y)) x := P.differentiableAt.comp x hv
  have h := fderiv_family_apply_point (fun y => P (v y)) w x X hPv hw
  have hP := fderiv_family_apply_point (fun _ : R3 => P) v x X (differentiableAt_const P) hv
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero] at hP
  change fderiv ℝ (fun y => P (v y) (w y)) x X = _
  rw [h, hP]
  rfl

/-- Differentiate an actual low pivot only from equality on a true neighborhood.
Fixed v,z are substituted after differentiation; no closed-room equality is differentiated. -/
theorem differentiated_low_pivot (P : H →L[ℝ] N →L[ℝ] ℝ)
    (I : E →L[ℝ] H) (J : H →L[ℝ] N)
    (PH : R3 → E →L[ℝ] H) (DL : R3 → H →L[ℝ] N) (x X : R3)
    (hPH : DifferentiableAt ℝ PH x) (hDL : DifferentiableAt ℝ DL x)
    (hPivot : ∀ᶠ y in 𝓝 x, ∀ v : E, ∀ z : H,
      P (I v) (DL y z) = -P (PH y v) (J z)) (v : E) (z : H) :
    P (I v) (directionalFDeriv X DL x z) =
      -P (directionalFDeriv X PH x v) (J z) := by
  let left : R3 → ℝ := fun y => P (I v) (DL y z)
  let right : R3 → ℝ := fun y => P (PH y v) (J z)
  have hDz : DifferentiableAt ℝ (fun y => DL y z) x := hDL.clm_apply (differentiableAt_const z)
  have hPv : DifferentiableAt ℝ (fun y => PH y v) x := hPH.clm_apply (differentiableAt_const v)
  have hleft : DifferentiableAt ℝ left x := (P (I v)).differentiableAt.comp x hDz
  have hright : DifferentiableAt ℝ right x :=
    (P.differentiableAt.comp x hPv).clm_apply (differentiableAt_const (J z))
  have heq : (fun y => left y+right y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hPivot] with y hy
    dsimp [left,right]
    rw [hy v z]
    ring
  have hd := congrArg (fun A : R3 →L[ℝ] ℝ => A X) heq.fderiv_eq
  have hfunadd : (fun y => left y+right y)=left+right := by funext y; rfl
  rw [hfunadd,fderiv_add hleft hright,fderiv_const_apply] at hd
  change directionalFDeriv X left x+directionalFDeriv X right x=0 at hd
  have hDzD : directionalFDeriv X (fun y => DL y z) x = directionalFDeriv X DL x z := by
    simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,
      map_zero,zero_add] using
      fderiv_family_apply_point DL (fun _ : R3 => z) x X hDL (differentiableAt_const z)
  have hPvD : directionalFDeriv X (fun y => PH y v) x = directionalFDeriv X PH x v := by
    simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,
      map_zero,zero_add] using
      fderiv_family_apply_point PH (fun _ : R3 => v) x X hPH (differentiableAt_const v)
  have hl : directionalFDeriv X left x = P (I v) (directionalFDeriv X DL x z) := by
    have hh := directional_bilinear_at P (fun _ : R3 => I v) (fun y => DL y z) x X
      (differentiableAt_const (I v)) hDz
    rw [hDzD] at hh
    simpa only [left,directionalFDeriv,fderiv_const_apply,
      ContinuousLinearMap.zero_apply,map_zero,add_zero] using hh
  have hr : directionalFDeriv X right x = P (directionalFDeriv X PH x v) (J z) := by
    have hh := directional_bilinear_at P (fun y => PH y v) (fun _ : R3 => J z) x X
      hPv (differentiableAt_const (J z))
    rw [hPvD] at hh
    simpa only [right,directionalFDeriv,fderiv_const_apply,
      ContinuousLinearMap.zero_apply,map_zero,zero_add] using hh
  rw [hl,hr] at hd
  linarith

/-- Two exact angular transposes move the derivative input to the Half slot.
Apply with a differentiated pair in either position to balance all four
coefficient-derivative terms; with ordinary pairs for both density terms. -/
theorem transpose_two_factors (P : H →L[ℝ] N →L[ℝ] ℝ)
    (I : E →L[ℝ] H) (J : H →L[ℝ] N)
    (PH1 PH2 : E →L[ℝ] H) (DL1 DL2 : H →L[ℝ] N)
    (hSym : ∀ a b : H, P a (J b)=P b (J a))
    (h1 : ∀ v : E, ∀ z : H, P (I v) (DL1 z)=-P (PH1 v) (J z))
    (h2 : ∀ v : E, ∀ z : H, P (I v) (DL2 z)=-P (PH2 v) (J z))
    (v w : E) :
    P (I v) (DL1 (PH2 w))=P (I w) (DL2 (PH1 v)) := by
  calc
    _ = -P (PH1 v) (J (PH2 w)) := h1 v (PH2 w)
    _ = -P (PH2 w) (J (PH1 v)) := congrArg Neg.neg (hSym (PH1 v) (PH2 w))
    _ = _ := (h2 w (PH1 v)).symm
end LocalPivot
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPWeakLower
