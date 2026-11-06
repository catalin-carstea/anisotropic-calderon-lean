import Calderon.NativeCoefficientWeakHalfLift
import Calderon.NativeHalfSmoothMultiplier

/-! This module proves a reduction, not zero-Dirichlet membership of the free harmonic product defect. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion NativeHalfSmoothMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma clm_multiplicationDefect_difference
    {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (P W : X →L[ℝ] U) (T : X →L[ℝ] X) (S : U →L[ℝ] U) (f : X) :
    (W (T f)-S (W f))-(P (T f)-S (P f)) =
      S (P f-W f)-(P (T f)-W (T f)) := by
  rw [map_sub]
  abel

attribute [local irreducible] nativeWeakHalfLift harmonicFirstOrderLiftCompletion
  nativeHalfSmoothMulL TauCeti.W1p.contDiffSMulL

variable (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
    ((volume : Measure R3).restrict ballOpens))
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
  (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
  (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)

lemma nativeWeakHalfLift_multiplication_defect_difference_mem_zero
    (f : SphereSobolev (1/2:ℝ)) :
    (nativeWeakHalfLift a b c hcoeff hF
        (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg f) -
      TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) m.1 m.2 hM hm hg (nativeWeakHalfLift a b c hcoeff hF f)) -
    (harmonicFirstOrderLiftCompletion hF
        (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg f) -
      TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) m.1 m.2 hM hm hg (harmonicFirstOrderLiftCompletion hF f)) ∈
    TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let P := harmonicFirstOrderLiftCompletion hF
  let W := nativeWeakHalfLift a b c hcoeff hF
  let T := nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) m.1 m.2 hM hm hg
  have hf : P f-W f ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    nativeWeakHalfLift_affine_difference a b c hcoeff hF f
  have hTf : P (T f)-W (T f) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    nativeWeakHalfLift_affine_difference a b c hcoeff hF (T f)
  have hSf : S (P f-W f) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    dsimp only [S]
    rw [TauCeti.W1p.contDiffSMulL_apply]
    exact TauCeti.W1p.contDiffSMul_mem_w1p0Submodule
      (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) m.2 hM hm hg hf
  have hid : (W (T f)-S (W f))-(P (T f)-S (P f)) =
      S (P f-W f)-(P (T f)-W (T f)) := by
    exact clm_multiplicationDefect_difference P W T S f
  change (W (T f)-S (W f))-(P (T f)-S (P f)) ∈
    TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2
  rw [hid]
  exact (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).sub_mem hSf hTf

lemma nativeWeakHalfLift_multiplication_defect_mem_zero_iff
    (f : SphereSobolev (1/2:ℝ)) :
    (nativeWeakHalfLift a b c hcoeff hF
        (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg f) -
      TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) m.1 m.2 hM hm hg (nativeWeakHalfLift a b c hcoeff hF f) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) ↔
    (harmonicFirstOrderLiftCompletion hF
        (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg f) -
      TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) m.1 m.2 hM hm hg (harmonicFirstOrderLiftCompletion hF f) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) := by
  let U : BallH1 := nativeWeakHalfLift a b c hcoeff hF
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg f) -
    TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) m.1 m.2 hM hm hg (nativeWeakHalfLift a b c hcoeff hF f)
  let V : BallH1 := harmonicFirstOrderLiftCompletion hF
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg f) -
    TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) m.1 m.2 hM hm hg (harmonicFirstOrderLiftCompletion hF f)
  let Z : Submodule ℝ BallH1 :=
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule
  have hd : U-V ∈ Z := nativeWeakHalfLift_multiplication_defect_difference_mem_zero
    a b c hcoeff hF hO hD τ0 m hM hm hg f
  change U ∈ Z ↔ V ∈ Z
  constructor
  · intro hU
    have hV := Z.sub_mem hU hd
    simpa only [sub_sub_cancel] using hV
  · intro hV
    have hU := Z.add_mem hd hV
    simpa only [sub_add_cancel] using hU

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_multiplication_defect_difference_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_multiplication_defect_mem_zero_iff

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.clm_multiplicationDefect_difference
