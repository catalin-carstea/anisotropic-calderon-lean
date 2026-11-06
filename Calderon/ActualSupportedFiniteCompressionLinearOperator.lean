import Calderon.ActualSupportedMeanZeroFiniteCore
import Calderon.ActualNativePhysicalOperatorLinearity
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConformalDepth
attribute [local irreducible] sphereSobolevInclusionL nativePacketPhysicalDensityOperator finiteCoreSobolevLift
  harmonicSphereSubspace sphereSobolevPartialSumL sphereSobolevZeroEquiv
variable (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L q delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:q∈Icc (0:ℝ) cover.dilationCeiling)
    (hRadius:∀ y∈interior cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (K:Set R3) (hK:IsClosed K) (hInside:K⊆interior cylinder)
    (n:ℕ) (T:smoothCompactFiniteSphereCore hO hD→smoothCompactFiniteSphereCore hO hD)
    (hT:∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      finiteHarmonicBand hO hD n (T A:R3→SphereL2) ∧ tsupport (T A:R3→SphereL2)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD ((T A:R3→SphereL2) y))=
        sphereSobolevPartialSumL (-(1/2:ℝ)) n
          (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y))
include hcalc hreg hF hO hD tau0 S L q delta Rstar p cover hd hRs hLam hRadius K hK hInside n T hT

theorem nativeFiniteCompression_add_on_supported_inputs
    (A B:smoothCompactFiniteSphereCore hO hD)
    (hA:tsupport (A:R3→SphereL2)⊆K) (hB:tsupport (B:R3→SphereL2)⊆K):
    T (A+B)=T A+T B := by
  have hAB:tsupport ((A+B:smoothCompactFiniteSphereCore hO hD):R3→SphereL2)⊆K:=
    tsupport_sphereL2_add_subset_of_closed K hK A B hA hB
  have hTA:tsupport (T A:R3→SphereL2)⊆K:=(hT A hA).2.1.trans hA
  have hTB:tsupport (T B:R3→SphereL2)⊆K:=(hT B hB).2.1.trans hB
  have hSum:tsupport (fun y=>(T A:R3→SphereL2) y+(T B:R3→SphereL2) y)⊆K:=
    tsupport_sphereL2_add_subset_of_closed K hK (T A) (T B) hTA hTB
  apply Subtype.ext
  apply eq_of_same_native_cover_negative_graph hO hD S L cover K hInside
    (T (A+B):R3→SphereL2) (fun y=>(T A:R3→SphereL2) y+(T B:R3→SphereL2) y)
    ((hT (A+B) hAB).2.1.trans hAB) hSum
    (fun i y=>sphereSobolevPartialSumL (-(1/2:ℝ)) n
      (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
        (finiteCoreSobolevLift hO hD (3/2:ℝ) (A+B)) i y)) (hT (A+B) hAB).2.2
  intro i y hy
  let J:SphereL2→L[ℝ]SphereSobolev (-(1/2:ℝ)):=
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
  let Pi:=sphereSobolevPartialSumL (-(1/2:ℝ)) n
  let Pfun:(R3→SphereSobolev (3/2:ℝ))→SphereSobolev (-(1/2:ℝ)):=
    fun u=>nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y
  let uA:=finiteCoreSobolevLift hO hD (3/2:ℝ) A
  let uB:=finiteCoreSobolevLift hO hD (3/2:ℝ) B
  have hPA:Pfun (finiteCoreSobolevLift hO hD (3/2:ℝ) (A+B))=Pfun uA+Pfun uB:=
    (congrArg Pfun (finiteCoreSobolevLift_add hO hD (3/2:ℝ) (by norm_num) A B)).trans
      (nativePacketPhysicalDensityOperator_add hcalc hreg hF hO hD tau0 S L q delta Rstar p cover
        hd hRs hLam i y hy.2 (hRadius y hy.1) uA uB
        (finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) A).1
        (finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) B).1)
  have hGA:J ((T A:R3→SphereL2) y)=Pi (Pfun uA):=(hT A hA).2.2 i y hy
  have hGB:J ((T B:R3→SphereL2) y)=Pi (Pfun uB):=(hT B hB).2.2 i y hy
  change J ((T A:R3→SphereL2) y+(T B:R3→SphereL2) y)=
    Pi (Pfun (finiteCoreSobolevLift hO hD (3/2:ℝ) (A+B)))
  exact (map_add J _ _).trans ((congrArg₂ (fun v w=>v+w) hGA hGB).trans
    ((map_add Pi (Pfun uA) (Pfun uB)).symm.trans (congrArg Pi hPA.symm)))

theorem nativeFiniteCompression_smul_on_supported_inputs
    (a:ℝ) (A:smoothCompactFiniteSphereCore hO hD)
    (hA:tsupport (A:R3→SphereL2)⊆K):T (a • A)=a • T A := by
  have haA:tsupport ((a • A:smoothCompactFiniteSphereCore hO hD):R3→SphereL2)⊆K:=
    tsupport_sphereL2_smul_subset_of_closed K hK a A hA
  have hTA:tsupport (T A:R3→SphereL2)⊆K:=(hT A hA).2.1.trans hA
  have hScaled:tsupport (fun y=>a • (T A:R3→SphereL2) y)⊆K:=
    tsupport_sphereL2_smul_subset_of_closed K hK a (T A) hTA
  apply Subtype.ext
  apply eq_of_same_native_cover_negative_graph hO hD S L cover K hInside
    (T (a • A):R3→SphereL2) (fun y=>a • (T A:R3→SphereL2) y)
    ((hT (a • A) haA).2.1.trans haA) hScaled
    (fun i y=>sphereSobolevPartialSumL (-(1/2:ℝ)) n
      (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
        (finiteCoreSobolevLift hO hD (3/2:ℝ) (a • A)) i y)) (hT (a • A) haA).2.2
  intro i y hy
  let J:SphereL2→L[ℝ]SphereSobolev (-(1/2:ℝ)):=
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
  let Pi:=sphereSobolevPartialSumL (-(1/2:ℝ)) n
  let Pfun:(R3→SphereSobolev (3/2:ℝ))→SphereSobolev (-(1/2:ℝ)):=
    fun u=>nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y
  let uA:=finiteCoreSobolevLift hO hD (3/2:ℝ) A
  have hPA:Pfun (finiteCoreSobolevLift hO hD (3/2:ℝ) (a • A))=a • Pfun uA:=
    (congrArg Pfun (finiteCoreSobolevLift_smul hO hD (3/2:ℝ) (by norm_num) a A)).trans
      (nativePacketPhysicalDensityOperator_smul hcalc hreg hF hO hD tau0 S L q delta Rstar p cover
        hd hRs hLam i y hy.2 (hRadius y hy.1) a uA
        (finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) A).1)
  have hGA:J ((T A:R3→SphereL2) y)=Pi (Pfun uA):=(hT A hA).2.2 i y hy
  change J (a • (T A:R3→SphereL2) y)=Pi (Pfun (finiteCoreSobolevLift hO hD (3/2:ℝ) (a • A)))
  exact (map_smul J a _).trans ((congrArg (fun v=>a • v) hGA).trans
    ((map_smul Pi a (Pfun uA)).symm.trans (congrArg Pi hPA.symm)))

theorem exists_nativeFiniteCompression_supported_meanZero_linearEnd
    (hKernel:UnitBallValueTraceKernel tau0) (hn:1 ≤ n):
    ∃ F:Module.End ℝ (supportedMeanZeroFiniteSphereCore hO hD K hK n),
      ∀ A:supportedMeanZeroFiniteSphereCore hO hD K hK n,(F A).val=T A.val := by
  let D:=supportedMeanZeroFiniteSphereCore hO hD K hK n
  let f:D→D:=fun A=>⟨T A.val,nativeFiniteCompression_mem_supportedMeanZeroFiniteSphereCore
    hcalc hreg hF hO hD tau0 hKernel S L q delta Rstar p cover hd hRs hLam hRadius K hK hInside n hn T hT A⟩
  let F:D→ₗ[ℝ]D:={
    toFun:=f
    map_add':=by
      intro A B
      apply Subtype.ext
      exact nativeFiniteCompression_add_on_supported_inputs hcalc hreg hF hO hD tau0 S L q delta Rstar p
        cover hd hRs hLam hRadius K hK hInside n T hT A.val B.val A.property.1 B.property.1
    map_smul':=by
      intro a A
      apply Subtype.ext
      exact nativeFiniteCompression_smul_on_supported_inputs hcalc hreg hF hO hD tau0 S L q delta Rstar p
        cover hd hRs hLam hRadius K hK hInside n T hT a A.val A.property.1}
  exact ⟨F,fun _=>rfl⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
