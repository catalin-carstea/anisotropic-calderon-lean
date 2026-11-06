import Calderon.ActualFullPhysicalOperatorFamily
import Calderon.ActualSupportedFiniteCompressionLinearOperator
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConformalDepth
attribute [local irreducible] sphereSobolevInclusionL nativePacketPhysicalDensityOperator finiteCoreSobolevLift
  harmonicSphereSubspace sphereSobolevZeroEquiv
variable (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L q delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:q∈Icc (0:ℝ) cover.dilationCeiling)
    (hRadius:∀ y∈interior cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (K:Set R3) (hK:IsClosed K) (hInside:K⊆interior cylinder)
    (F:smoothCompactFiniteSphereCore hO hD→R3→SphereL2)
    (hFData:∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      ContDiff ℝ ∞ (F A) ∧ HasCompactSupport (F A) ∧ tsupport (F A)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F A y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y)
include hcalc hreg hF hO hD tau0 S L q delta Rstar p cover hd hRs hLam hRadius K hK hInside F hFData

theorem actualFullPhysicalFamily_add_on_supported_inputs
    (A B:smoothCompactFiniteSphereCore hO hD)
    (hA:tsupport (A:R3→SphereL2)⊆K) (hB:tsupport (B:R3→SphereL2)⊆K):
    F (A+B)=(fun y=>F A y+F B y) := by
  have hAB:tsupport ((A+B:smoothCompactFiniteSphereCore hO hD):R3→SphereL2)⊆K:=
    tsupport_sphereL2_add_subset_of_closed K hK A B hA hB
  have hSum:tsupport (fun y=>F A y+F B y)⊆K:=tsupport_sphereL2_add_subset_of_closed K hK
    (F A) (F B) ((hFData A hA).2.2.1.trans hA) ((hFData B hB).2.2.1.trans hB)
  apply eq_of_same_native_cover_negative_graph hO hD S L cover K hInside
    (F (A+B)) (fun y=>F A y+F B y) ((hFData (A+B) hAB).2.2.1.trans hAB) hSum
    (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
      (finiteCoreSobolevLift hO hD (3/2:ℝ) (A+B))) (hFData (A+B) hAB).2.2.2
  intro i y hy
  let J:SphereL2→L[ℝ]SphereSobolev (-(1/2:ℝ)):=
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
  let Pfun:(R3→SphereSobolev (3/2:ℝ))→SphereSobolev (-(1/2:ℝ)):=
    fun u=>nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y
  let uA:=finiteCoreSobolevLift hO hD (3/2:ℝ) A
  let uB:=finiteCoreSobolevLift hO hD (3/2:ℝ) B
  have hP:Pfun (finiteCoreSobolevLift hO hD (3/2:ℝ) (A+B))=Pfun uA+Pfun uB:=
    (congrArg Pfun (finiteCoreSobolevLift_add hO hD (3/2:ℝ) (by norm_num) A B)).trans
      (nativePacketPhysicalDensityOperator_add hcalc hreg hF hO hD tau0 S L q delta Rstar p cover
        hd hRs hLam i y hy.2 (hRadius y hy.1) uA uB
        (finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) A).1
        (finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) B).1)
  have hGA:J (F A y)=Pfun uA:=(hFData A hA).2.2.2 i y hy
  have hGB:J (F B y)=Pfun uB:=(hFData B hB).2.2.2 i y hy
  change J (F A y+F B y)=Pfun (finiteCoreSobolevLift hO hD (3/2:ℝ) (A+B))
  exact (map_add J _ _).trans ((congrArg₂ (fun a b=>a+b) hGA hGB).trans hP.symm)

theorem actualFullPhysicalFamily_smul_on_supported_inputs
    (a:ℝ) (A:smoothCompactFiniteSphereCore hO hD) (hA:tsupport (A:R3→SphereL2)⊆K):
    F (a • A)=(fun y=>a • F A y) := by
  have haA:tsupport ((a • A:smoothCompactFiniteSphereCore hO hD):R3→SphereL2)⊆K:=
    tsupport_sphereL2_smul_subset_of_closed K hK a A hA
  have hScaled:tsupport (fun y=>a • F A y)⊆K:=tsupport_sphereL2_smul_subset_of_closed K hK
    a (F A) ((hFData A hA).2.2.1.trans hA)
  apply eq_of_same_native_cover_negative_graph hO hD S L cover K hInside
    (F (a • A)) (fun y=>a • F A y) ((hFData (a • A) haA).2.2.1.trans haA) hScaled
    (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
      (finiteCoreSobolevLift hO hD (3/2:ℝ) (a • A))) (hFData (a • A) haA).2.2.2
  intro i y hy
  let J:SphereL2→L[ℝ]SphereSobolev (-(1/2:ℝ)):=
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
  let Pfun:(R3→SphereSobolev (3/2:ℝ))→SphereSobolev (-(1/2:ℝ)):=
    fun u=>nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y
  let uA:=finiteCoreSobolevLift hO hD (3/2:ℝ) A
  have hP:Pfun (finiteCoreSobolevLift hO hD (3/2:ℝ) (a • A))=a • Pfun uA:=
    (congrArg Pfun (finiteCoreSobolevLift_smul hO hD (3/2:ℝ) (by norm_num) a A)).trans
      (nativePacketPhysicalDensityOperator_smul hcalc hreg hF hO hD tau0 S L q delta Rstar p cover
        hd hRs hLam i y hy.2 (hRadius y hy.1) a uA
        (finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) A).1)
  have hGA:J (F A y)=Pfun uA:=(hFData A hA).2.2.2 i y hy
  change J (a • F A y)=Pfun (finiteCoreSobolevLift hO hD (3/2:ℝ) (a • A))
  exact (map_smul J a _).trans ((congrArg (fun v=>a • v) hGA).trans hP.symm)

theorem exists_actualFullPhysicalFamily_supported_meanZero_linearMap
    (hKernel:UnitBallValueTraceKernel tau0) (n:ℕ):
    ∃ E:(supportedMeanZeroFiniteSphereCore hO hD K hK n)→ₗ[ℝ](R3→SphereL2),
      (∀ A:supportedMeanZeroFiniteSphereCore hO hD K hK n,E A=F A.val) ∧
      ∀ A:supportedMeanZeroFiniteSphereCore hO hD K hK n,
      ContDiff ℝ ∞ (E A) ∧ HasCompactSupport (E A) ∧ tsupport (E A)⊆K ∧
        ∀ y:R3,sphereMean (E A y)=0 := by
  let E:(supportedMeanZeroFiniteSphereCore hO hD K hK n)→ₗ[ℝ](R3→SphereL2):={
    toFun:=fun A=>F A.val
    map_add':=by
      intro A B
      exact actualFullPhysicalFamily_add_on_supported_inputs hcalc hreg hF hO hD tau0 S L q delta Rstar p
        cover hd hRs hLam hRadius K hK hInside F hFData A.val B.val A.property.1 B.property.1
    map_smul':=by
      intro a A
      exact actualFullPhysicalFamily_smul_on_supported_inputs hcalc hreg hF hO hD tau0 S L q delta Rstar p
        cover hd hRs hLam hRadius K hK hInside F hFData a A.val A.property.1}
  refine ⟨E,fun _=>rfl,?_⟩
  intro A
  have hOut:=hFData A.val A.property.1
  refine ⟨hOut.1,hOut.2.1,hOut.2.2.1.trans A.property.1,?_⟩
  exact sphereMean_native_finite_physical_output_eq_zero hcalc hreg hF hO hD tau0 hKernel
    S L q delta Rstar p cover hd hRs hLam hRadius K hInside A.val A.property.2.2
    (F A.val) (hOut.2.2.1.trans A.property.1) hOut.2.2.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
