import Calderon.NativeCoefficientWeakHalfLift

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Actual zero-space injectivity identifies homogeneous affine weak solutions. -/

lemma nativeH1_affine_difference_mem_zero (P U V : BallH1)
    (hU : P-U ∈ TauCeti.w1p0Submodule volume ballOpens 2)
    (hV : P-V ∈ TauCeti.w1p0Submodule volume ballOpens 2) :
    U-V ∈ TauCeti.w1p0Submodule volume ballOpens 2 := by
  have he : U-V = (P-V)-(P-U) := by abel
  exact he.symm ▸ (TauCeti.w1p0Submodule volume ballOpens 2).toSubmodule.sub_mem hV hU

lemma eq_of_nativeEnergy_kernel_zero_difference
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (hA : A.IsInvertible)
    (E : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (hRestrict : ∀ (u v : BallH1Zero), E (u : BallH1) v = A u v)
    (U V : BallH1) (hDiff : U-V ∈ TauCeti.w1p0Submodule volume ballOpens 2)
    (hU : ∀ v : BallH1Zero, E U v = 0) (hV : ∀ v : BallH1Zero, E V v = 0) : U = V := by
  let z : BallH1Zero := ⟨U-V,hDiff⟩
  have hzA : A z = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have he := congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) (E.map_sub U V)
    have hc := congrArg₂ (fun x y : ℝ => x-y) (hU v) (hV v)
    exact (hRestrict z v).symm.trans (he.trans (hc.trans (sub_self 0)))
  have hz : z = 0 := hA.injective (hzA.trans A.map_zero.symm)
  have hValue : U-V = 0 := congrArg (fun u : BallH1Zero => (u : BallH1)) hz
  exact sub_eq_zero.mp hValue

attribute [local irreducible] nativeZeroCoefficientEnergyL nativeCoefficientWeakEnergyL
  nativeWeakHalfLift harmonicFirstOrderLiftCompletion

lemma nativeWeakHalfLift_unique
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (hF : SphereFischerInner)
    (hi : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff).IsInvertible)
    (f : SphereSobolev (1/2:ℝ)) (U : BallH1)
    (hZero : harmonicFirstOrderLiftCompletion hF f-U ∈ TauCeti.w1p0Submodule volume ballOpens 2)
    (hWeak : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a b c U (v : BallH1) = 0) :
    nativeWeakHalfLift a b c hcoeff hF f = U := by
  let A := nativeZeroCoefficientEnergyL a b c hcoeff
  let E := nativeCoefficientWeakEnergyL a b c hcoeff
  let W := nativeWeakHalfLift a b c hcoeff hF f
  have hA : A.IsInvertible := (nativeZeroCoefficientEnergyL_isInvertible_iff a b c hcoeff).mpr hi
  have hRestrict : ∀ (u v : BallH1Zero), E (u : BallH1) v = A u v := by
    intro u v
    exact (nativeCoefficientWeakEnergyL_restriction a b c hcoeff u v).symm.trans
      (nativeZeroCoefficientEnergyL_apply a b c hcoeff u v).symm
  have hDiff : W-U ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
    nativeH1_affine_difference_mem_zero (harmonicFirstOrderLiftCompletion hF f) W U
      (nativeWeakHalfLift_affine_difference a b c hcoeff hF f) hZero
  have hW : ∀ v : BallH1Zero, E W v = 0 := by
    intro v
    exact (nativeCoefficientWeakEnergyL_apply a b c hcoeff W v).trans
      (nativeWeakHalfLift_weak_solution a b c hcoeff hF hi f v)
  have hU : ∀ v : BallH1Zero, E U v = 0 := by
    intro v
    exact (nativeCoefficientWeakEnergyL_apply a b c hcoeff U v).trans (hWeak v)
  exact eq_of_nativeEnergy_kernel_zero_difference A hA E hRestrict W U hDiff hW hU

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1_affine_difference_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eq_of_nativeEnergy_kernel_zero_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_unique
