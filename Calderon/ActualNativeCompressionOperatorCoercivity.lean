import Calderon.ActualNativeFiniteCompressedCoercivity
import Calderon.ActualWholeCoverPhysicalOutputUniqueness
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore ReferenceDensityBounds
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevPartialSumL finiteCoreSobolevLift
  harmonicSphereSubspace nativePacketPhysicalDensityOperator

theorem nativeCompressionCoreBound_of_actual_operator_contracts
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics)
    (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData)
    (L:ℝ) (cover:NativeNormalCover S L) (chi:R3→ℝ) (hSupp:tsupport chi⊆interior cylinder)
    (q delta Rstar:ℝ) (p:ℕ) (c:ℝ) (n0:ℕ)
    (T:ℕ→smoothCompactFiniteSphereCore hO hD→R3→SphereL2)
    (hSupport:∀ n:ℕ,max 1 n0 ≤ n → ∀ A:smoothCompactFiniteSphereCore hO hD,
      finiteHarmonicBand hO hD n (A:R3→SphereL2) → tsupport (A:R3→SphereL2)⊆tsupport chi →
      (∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) → tsupport (T n A)⊆tsupport chi)
    (hGraph:∀ n:ℕ,max 1 n0 ≤ n → ∀ A:smoothCompactFiniteSphereCore hO hD,
      finiteHarmonicBand hO hD n (A:R3→SphereL2) → tsupport (A:R3→SphereL2)⊆tsupport chi →
      (∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) →
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (T n A y))=
        sphereSobolevPartialSumL (-(1/2:ℝ)) n
          (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y))
    (hBound:∀ n:ℕ,max 1 n0 ≤ n → ∀ A:smoothCompactFiniteSphereCore hO hD,
      finiteHarmonicBand hO hD n (A:R3→SphereL2) → tsupport (A:R3→SphereL2)⊆tsupport chi →
      (∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) →
      c*(∫ y,referenceDensityFamily S.g1 L (q,y)*‖(A:R3→SphereL2) y‖^2) ≤
        ∫ y,referenceDensityFamily S.g1 L (q,y)*‖T n A y‖^2):
    NativeFinitePhysicalCompressionCoreBound hcalc hF hO hD tau0 S L cover chi q delta Rstar p c n0 := by
  intro n hn A hBandA hASupp hMean B _hBandB hBSupp hBGraph
  have hSame:(B:R3→SphereL2)=T n A :=
    eq_of_same_native_cover_negative_graph hO hD S L cover (tsupport chi) hSupp
      (B:R3→SphereL2) (T n A) hBSupp (hSupport n hn A hBandA hASupp hMean)
      (fun i y=>sphereSobolevPartialSumL (-(1/2:ℝ)) n
        (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y))
      hBGraph (hGraph n hn A hBandA hASupp hMean)
  simpa only [hSame] using hBound n hn A hBandA hASupp hMean

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
