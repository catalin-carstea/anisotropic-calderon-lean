import Calderon.NativeSupportedAdjointH2Inverse
import Calderon.NativeAdjointRepresentativeForcingAlignmentDiagnostic
import Calderon.NativeSupportedAdjointStrongForcing
import Calderon.NativeCoefficientWeakHalfLift
import Calderon.NativeHarmonicLiftOrderCoherence
import Calderon.CoefficientMatrixRegularity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion
  NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Fully expanded before source in native-supported-adjoint-nonzero-H2-author-oct14-v001/EXPANSION-v001.json.
Exact three-half datum, literal formal-adjoint coefficients and same harmonic completion. -/

def nativeH2AffineCorrectionL (J : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2)
    (R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (S : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (P : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2) :
    SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 :=
  ((ContinuousLinearMap.id ℝ (BallSobolev 2))-J.comp (R.comp S)).comp P

lemma nativeH2AffineCorrectionL_apply (J : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2)
    (R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (S : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (P : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2) (f : SphereSobolev (3/2:ℝ)) :
    nativeH2AffineCorrectionL J R S P f = P f-J (R (S (P f))) := rfl

lemma nativeH2AffineCorrection_firstOrder (J : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2)
    (R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (S : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (P : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2)
    (hJ : ∀ z : StrongDirichletSpace 0, TauCeti.Wkp.firstOrder 1 (J z) =
      (strongDirichletProjectionL 0 z : BallH1)) (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (nativeH2AffineCorrectionL J R S P f) =
      TauCeti.Wkp.firstOrder 1 (P f)-
        (strongDirichletProjectionL 0 (R (S (P f))) : BallH1) := by
  let L := TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1
  have he := congrArg (fun U : BallSobolev 2 => L U) (nativeH2AffineCorrectionL_apply J R S P f)
  have hs := L.map_sub (P f) (J (R (S (P f))))
  exact he.trans (hs.trans (congrArg (fun z : BallH1 => L (P f)-z) (hJ (R (S (P f))))))

lemma nativeH2AffineCorrection_firstOrder_difference (J : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2)
    (R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (S : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (P : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2)
    (hJ : ∀ z : StrongDirichletSpace 0, TauCeti.Wkp.firstOrder 1 (J z) =
      (strongDirichletProjectionL 0 z : BallH1)) (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (P f)-
      TauCeti.Wkp.firstOrder 1 (nativeH2AffineCorrectionL J R S P f) =
        (strongDirichletProjectionL 0 (R (S (P f))) : BallH1) := by
  rw [nativeH2AffineCorrection_firstOrder J R S P hJ f]
  abel

lemma nativeH2AffineCorrection_zero_difference (J : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2)
    (R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (S : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (P : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2)
    (hJ : ∀ z : StrongDirichletSpace 0, TauCeti.Wkp.firstOrder 1 (J z) =
      (strongDirichletProjectionL 0 z : BallH1)) (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (P f)-
      TauCeti.Wkp.firstOrder 1 (nativeH2AffineCorrectionL J R S P f) ∈
        TauCeti.w1p0Submodule volume ballOpens 2 := by
  rw [nativeH2AffineCorrection_firstOrder_difference J R S P hJ f]
  exact (strongDirichletProjectionL 0 (R (S (P f)))).property

lemma nativeH2AffineCorrection_kernel (J : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2)
    (R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (S : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (P : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2)
    (hJ : ∀ z : StrongDirichletSpace 0, TauCeti.Wkp.firstOrder 1 (J z) =
      (strongDirichletProjectionL 0 z : BallH1))
    (Q : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (hS : ∀ (U : BallSobolev 2) (v : BallH1Zero), Q (TauCeti.Wkp.firstOrder 1 U) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (S U) v)
    (hR : ∀ (f : BallSobolev 0) (v : BallH1Zero),
      Q (strongDirichletProjectionL 0 (R f) : BallH1) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v)
    (f : SphereSobolev (3/2:ℝ)) (v : BallH1Zero) :
    Q (TauCeti.Wkp.firstOrder 1 (nativeH2AffineCorrectionL J R S P f)) v = 0 := by
  have he := congrArg (fun u : BallH1 => Q u v)
    (nativeH2AffineCorrection_firstOrder J R S P hJ f)
  have hs := congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v)
    (Q.map_sub (TauCeti.Wkp.firstOrder 1 (P f))
      (strongDirichletProjectionL 0 (R (S (P f))) : BallH1))
  have hc := congrArg₂ (fun x y : ℝ => x-y) (hS (P f) v) (hR (S (P f)) v)
  exact he.trans (hs.trans (hc.trans (sub_self _)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2AffineCorrectionL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2AffineCorrectionL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2AffineCorrection_firstOrder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2AffineCorrection_firstOrder_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2AffineCorrection_zero_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2AffineCorrection_kernel
