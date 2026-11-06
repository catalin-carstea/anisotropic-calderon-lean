import Calderon.ActualNativeFiniteCompressionFamily
import Calderon.ActualNativePhysicalOutputMeanZero
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConformalDepth

theorem tsupport_sphereL2_add_subset_of_closed
    (K:Set R3) (hK:IsClosed K) (f g:R3→SphereL2)
    (hf:tsupport f⊆K) (hg:tsupport g⊆K):tsupport (fun y=>f y+g y)⊆K := by
  apply closure_minimal ?_ hK
  intro y hy
  by_contra hk
  have hf0:f y=0:=image_eq_zero_of_notMem_tsupport (fun hh=>hk (hf hh))
  have hg0:g y=0:=image_eq_zero_of_notMem_tsupport (fun hh=>hk (hg hh))
  exact hy (by change f y+g y=0;rw [hf0,hg0,add_zero])

theorem tsupport_sphereL2_smul_subset_of_closed
    (K:Set R3) (hK:IsClosed K) (a:ℝ) (f:R3→SphereL2)
    (hf:tsupport f⊆K):tsupport (fun y=>a • f y)⊆K := by
  apply closure_minimal ?_ hK
  intro y hy
  by_contra hk
  have hf0:f y=0:=image_eq_zero_of_notMem_tsupport (fun hh=>hk (hf hh))
  exact hy (by change a • f y=0;rw [hf0,smul_zero])

def supportedMeanZeroFiniteSphereCore
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (K:Set R3) (hK:IsClosed K) (n:ℕ):Submodule ℝ (smoothCompactFiniteSphereCore hO hD) where
  carrier:={A | tsupport (A:R3→SphereL2)⊆K ∧ finiteHarmonicBand hO hD n (A:R3→SphereL2) ∧
    ∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0}
  zero_mem':=by
    refine ⟨?_,?_,?_⟩
    · change tsupport (fun _ :R3=>(0:SphereL2))⊆K
      simp
    · intro y k _
      exact map_zero (sphereHarmonicCoordinate hO hD k)
    · intro y
      exact map_zero sphereMean
  add_mem':=by
    intro A B hA hB
    refine ⟨tsupport_sphereL2_add_subset_of_closed K hK A B hA.1 hB.1,?_,?_⟩
    · intro y k hk
      change sphereHarmonicCoordinate hO hD k ((A:R3→SphereL2) y+(B:R3→SphereL2) y)=0
      rw [map_add,hA.2.1 y k hk,hB.2.1 y k hk,add_zero]
    · intro y
      change sphereMean ((A:R3→SphereL2) y+(B:R3→SphereL2) y)=0
      rw [map_add,hA.2.2 y,hB.2.2 y,add_zero]
  smul_mem':=by
    intro a A hA
    refine ⟨tsupport_sphereL2_smul_subset_of_closed K hK a A hA.1,?_,?_⟩
    · intro y k hk
      change sphereHarmonicCoordinate hO hD k (a • (A:R3→SphereL2) y)=0
      rw [map_smul,hA.2.1 y k hk,smul_zero]
    · intro y
      change sphereMean (a • (A:R3→SphereL2) y)=0
      rw [map_smul,hA.2.2 y,smul_zero]

theorem nativeFiniteCompression_mem_supportedMeanZeroFiniteSphereCore
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L q delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:q∈Icc (0:ℝ) cover.dilationCeiling)
    (hRadius:∀ y∈interior cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (K:Set R3) (hK:IsClosed K) (hInside:K⊆interior cylinder)
    (n:ℕ) (hn:1 ≤ n)
    (T:smoothCompactFiniteSphereCore hO hD→smoothCompactFiniteSphereCore hO hD)
    (hT:∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      finiteHarmonicBand hO hD n (T A:R3→SphereL2) ∧ tsupport (T A:R3→SphereL2)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD ((T A:R3→SphereL2) y))=
        sphereSobolevPartialSumL (-(1/2:ℝ)) n
          (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y))
    (A:supportedMeanZeroFiniteSphereCore hO hD K hK n):
    T A.val∈supportedMeanZeroFiniteSphereCore hO hD K hK n := by
  have hOut:=hT A.val A.property.1
  refine ⟨hOut.2.1.trans A.property.1,hOut.1,?_⟩
  exact sphereMean_native_finite_compressed_physical_output_eq_zero hcalc hreg hF hO hD tau0 hKernel
    S L q delta Rstar p cover hd hRs hLam hRadius K hInside A.val A.property.2.2
    n hn (T A.val:R3→SphereL2) (hOut.2.1.trans A.property.1) hOut.2.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
