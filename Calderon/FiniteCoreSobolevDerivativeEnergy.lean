import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.FiniteCoreH1BesselNorm
import Calderon.ActualFiniteHarmonicCoreBase
import Calderon.ActualFiniteHarmonicModelSourceEnergy
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph PrincipalCommutator
  ReferenceDensityBounds ActualFiniteHarmonicModel

lemma directionalFDeriv_finiteCoreSobolevLift
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (X x : R3) :
    directionalFDeriv X (finiteCoreSobolevLift hO hD s F) x =
      finiteCoreSobolevLift hO hD s (coreDirectionalDerivative hO hD X F) x := by
  let u := finiteCoreSobolevLift hO hD s F
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD s F
  apply sphereSobolev_ext s
  intro k
  let C := sphereSobolevCoefficientL s k
  let P := sphereHarmonicCoordinate hO hD k
  have hNativeMap : fderiv ℝ (fun y => C (u y)) x = C.comp (fderiv ℝ u x) :=
    (C.hasFDerivAt.comp x ((hu.differentiable (by simp) x).hasFDerivAt)).fderiv
  have hPhysicalMap : fderiv ℝ (fun y => P (F.val y)) x = P.comp (fderiv ℝ F.val x) :=
    (P.hasFDerivAt.comp x ((F.property.1.differentiable (by simp) x).hasFDerivAt)).fderiv
  have hFunctions : (fun y => C (u y)) = (fun y => P (F.val y)) :=
    funext (fun y => sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD s F y k)
  have hNative : C (directionalFDeriv X u x) =
      directionalFDeriv X (fun y => C (u y)) x := by
    simpa only [directionalFDeriv,ContinuousLinearMap.comp_apply] using
      (congrArg (fun A : R3 →L[ℝ] harmonicSphereSubspace k => A X) hNativeMap).symm
  have hPhysical : directionalFDeriv X (fun y => P (F.val y)) x =
      P (directionalFDeriv X F.val x) := by
    simpa only [directionalFDeriv,ContinuousLinearMap.comp_apply] using
      congrArg (fun A : R3 →L[ℝ] harmonicSphereSubspace k => A X) hPhysicalMap
  calc
    _ = directionalFDeriv X (fun y => C (u y)) x := hNative
    _ = directionalFDeriv X (fun y => P (F.val y)) x :=
      congrArg (fun f : R3 → harmonicSphereSubspace k => directionalFDeriv X f x) hFunctions
    _ = P (directionalFDeriv X F.val x) := hPhysical
    _ = _ := (sphereSobolevCoefficientL_finiteCoreSobolevLift
      hO hD s (coreDirectionalDerivative hO hD X F) x k).symm

lemma native_threeHalf_angular_energy_le_finiteCoreSourceEnergy
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    beta⁻¹*(∑ a : Fin 3, ‖Iin (directionalFDeriv (coordinateDirection a) u x)‖^2)+
      beta*‖u x‖^2 ≤ finiteCoreSourceEnergy hO hD beta F x := by
  intro u Iin
  have hGradient (a : Fin 3) : Iin (directionalFDeriv (coordinateDirection a) u x) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ)
        (coreDirectionalDerivative hO hD (coordinateDirection a) F) x :=
    (congrArg Iin (directionalFDeriv_finiteCoreSobolevLift
      hO hD (3/2 : ℝ) F (coordinateDirection a) x)).trans
        (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
          (by norm_num) (coreDirectionalDerivative hO hD (coordinateDirection a) F) x)
  have hSum : (∑ a : Fin 3, ‖Iin (directionalFDeriv (coordinateDirection a) u x)‖^2) =
      ∑ a : Fin 3, ‖(coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (coreDirectionalDerivative hO hD (coordinateDirection a) F)).val x‖^2 := by
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun r : ℝ => r^2)
      ((congrArg norm (hGradient a)).trans (norm_finiteCoreSobolevLift hO hD (1/2 : ℝ)
        (coreDirectionalDerivative hO hD (coordinateDirection a) F) x))
  have hValue : ‖u x‖^2 =
      ‖(coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x‖^2 :=
    congrArg (fun r : ℝ => r^2) (norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)
  have hEnergy := congrArg₂ (fun a b : ℝ => beta⁻¹*a+beta*b) hSum hValue
  have hBound := SectionFiveErrorForms.angular_error_terms_le_sourceNormSquareIntegrand beta
    (fun a : Fin 3 => (coreDirectionalDerivative hO hD (coordinateDirection a) F).val x)
    ((coreWeightOperator hO hD (besselWeight 1) F).val x)
    (fun a : Fin 3 => (coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (coreDirectionalDerivative hO hD (coordinateDirection a) F)).val x)
    ((coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F).val x)
  exact hEnergy.trans_le hBound

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore

#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.directionalFDeriv_finiteCoreSobolevLift
#print axioms OAI.AnisotropicCalderon.ActualFiniteHarmonicCore.native_threeHalf_angular_energy_le_finiteCoreSourceEnergy
