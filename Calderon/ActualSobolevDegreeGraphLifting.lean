import Calderon.SphereSobolevBesselOrderCompatibility
import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.ActualFiniteHarmonicCoreWeights
import Calderon.ActualFiniteCoreSobolevLift

/-! Source-only author: actualSol, 29 October 2026. UNCOMPILED.
Before-source expansion and exact source/provider bindings: MATHEMATICS.md/BINDINGS.json.
Three physical-degree/Bessel wrappers only; no norm change, output finiteness or signed estimate. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic.DegreeGraphLifting
open SpectralWeightedGraph SpectralCoreRegularity SphereHilbertDecomposition
  ActualFiniteHarmonicCore

local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "JH" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevBesselOrderL
  sphereSobolevShiftedDegreeL finiteCoreSobolevLift coreWeightOperator

/-- Physical degree plus the original inclusion is Bessel order one; the zero mode is retained.
The displayed degree map has its equal-valued output order read explicitly as `-1/2`. -/
lemma sphereSobolevShiftedDegreeL_add_inclusion_half :
    (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg) + JH =
      sphereSobolevBesselOrderL (1/2 : ℝ) (-(1/2 : ℝ)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro k
  have hIndex : sphereSobolevCoefficientL (-(1/2 : ℝ)) k
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) v) =
      sphereSobolevCoefficientL ((1/2 : ℝ)-1) k
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) v) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s k
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) v))
        (show (-(1/2 : ℝ)) = (1/2 : ℝ)-1 by norm_num)
  have hDegree := hIndex.trans (sphereSobolevCoefficientL_shiftedDegree (1/2 : ℝ) k v)
  have hJ := sphereSobolevCoefficientL_inclusion (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v k
  have hBessel := sphereSobolevCoefficientL_besselOrder (1/2 : ℝ) (-(1/2 : ℝ)) v k
  have hWeight : besselWeight ((1/2 : ℝ)-(-(1/2 : ℝ))) k = 1 + (k : ℝ) := by
    rw [show (1/2 : ℝ)-(-(1/2 : ℝ)) = 1 by norm_num]
    simp only [besselWeight, Real.rpow_one]
  calc
    sphereSobolevCoefficientL (-(1/2 : ℝ)) k
        (((sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg) + JH) v) =
        sphereSobolevCoefficientL (-(1/2 : ℝ)) k (sphereSobolevShiftedDegreeL (1/2 : ℝ) v) +
          sphereSobolevCoefficientL (-(1/2 : ℝ)) k (JH v) :=
      (sphereSobolevCoefficientL (-(1/2 : ℝ)) k).map_add _ _
    _ = (k : ℝ) • sphereSobolevCoefficientL (1/2 : ℝ) k v +
          sphereSobolevCoefficientL (1/2 : ℝ) k v :=
      congrArg₂ (fun a b : harmonicSphereSubspace k => a+b) hDegree hJ
    _ = (1 + (k : ℝ)) • sphereSobolevCoefficientL (1/2 : ℝ) k v := by
      rw [add_smul, one_smul]
      exact add_comm _ _
    _ = sphereSobolevCoefficientL (-(1/2 : ℝ)) k
        (sphereSobolevBesselOrderL (1/2 : ℝ) (-(1/2 : ℝ)) v) :=
      (hBessel.trans (congrArg
        (fun a : ℝ => a • sphereSobolevCoefficientL (1/2 : ℝ) k v) hWeight)).symm

/-- An arbitrary Half degree graph gives this explicit Hi lift, without finite output. -/
lemma inclusion_besselOrder_eq_of_half_degree_graph (v z0 : Half)
    (hDegree : (sphereSobolevShiftedDegreeL (1/2 : ℝ) v : Neg) = JH z0) :
    IH (sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ) (z0+v)) = v := by
  let Lplus : Half →L[ℝ] Neg := sphereSobolevBesselOrderL (1/2 : ℝ) (-(1/2 : ℝ))
  let Lminus : Half →L[ℝ] Hi := sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)
  let Linverse : Neg →L[ℝ] Half := sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)
  have hAt : (sphereSobolevShiftedDegreeL (1/2 : ℝ) v : Neg) + JH v = Lplus v :=
    congrArg (fun A : Half →L[ℝ] Neg => A v)
      sphereSobolevShiftedDegreeL_add_inclusion_half
  have hSum : (sphereSobolevShiftedDegreeL (1/2 : ℝ) v : Neg) + JH v = JH (z0+v) :=
    (congrArg (fun z : Neg => z + JH v) hDegree).trans (((JH).map_add z0 v).symm)
  have hPlus : Lplus v = JH (z0+v) := hAt.symm.trans hSum
  have hTransport : (IH).comp Lminus = Linverse.comp JH :=
    sphereSobolevBesselOrderL_inclusion_comp (1/2 : ℝ) (-(1/2 : ℝ)) (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (by norm_num) (by norm_num)
  have hTransportAt : IH (Lminus (z0+v)) = Linverse (JH (z0+v)) :=
    congrArg (fun A : Half →L[ℝ] Half => A (z0+v)) hTransport
  have hInverseAt : Linverse (Lplus v) = v :=
    congrArg (fun A : Half →L[ℝ] Half => A v)
      (sphereSobolevBesselOrderL_inverse (1/2 : ℝ) (-(1/2 : ℝ)))
  exact hTransportAt.trans ((congrArg Linverse hPlus.symm).trans hInverseAt)

/-- The original finite-core physical degree supplies the Hi input for its Half output. -/
lemma inclusion_finiteCoreSobolevLift_coreDegree
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F0) x) =
      (sphereSobolevShiftedDegreeL (3/2 : ℝ)
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x) : Half) := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  have hCore : sphereHarmonicCoordinate hO hD k ((coreDegree hO hD F0).val x) =
      (k : ℝ) • sphereHarmonicCoordinate hO hD k (F0.val x) := by
    simpa only [coreDegree] using
      (coreWeightOperator_graph hO hD (fun n : ℕ => (n : ℝ)) F0 x k)
  have hLeft1 := sphereSobolevCoefficientL_inclusion (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F0) x) k
  have hLeft2 := sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ)
    (coreDegree hO hD F0) x k
  have hLeft := hLeft1.trans (hLeft2.trans hCore)
  have hIndex : sphereSobolevCoefficientL (1/2 : ℝ) k
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x)) =
      sphereSobolevCoefficientL ((3/2 : ℝ)-1) k
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x)) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s k
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x)))
        (show (1/2 : ℝ) = (3/2 : ℝ)-1 by norm_num)
  have hRight1 := sphereSobolevCoefficientL_shiftedDegree (3/2 : ℝ) k
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x)
  have hRight2 := sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 x k
  have hRight := hIndex.trans (hRight1.trans (congrArg
    (fun z : harmonicSphereSubspace k => (k : ℝ) • z) hRight2))
  exact hLeft.trans hRight.symm

end OAI.AnisotropicCalderon.SphereHarmonic.DegreeGraphLifting
