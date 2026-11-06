import Calderon.ActualJacobiCompactSmoothExtension
import Calderon.NativeThreeHalfBoundaryMultiplierLocalSmoothness

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-JACOBI-COMPACT-EXTENSION-ROOM-EXPANSION-v001.md. Actual scalar choice occurs before the finite cutoff. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

structure ReferenceJacobiCompactExtensionRoom
    (F : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3)
    (K : Set (ℝ × (R3 × ℝ))) where
  scalar : Fin 3 → Fin 3 → ((ℝ × (R3 × ℝ)) × R3) → ℝ
  smooth : ∀ i j, ContDiff ℝ ∞ (scalar i j)
  compactSupport : ∀ i j, HasCompactSupport (scalar i j)
  sphereEq : ∀ p ∈ K, ∀ i j : Fin 3, ∀ᶠ t in 𝓝 p, ∀ x : UnitSphere,
    scalar i j (t,x.val) = coefficientValue 3 (F i j t) x.val

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
variable {F : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3}
  {K : Set (ℝ × (R3 × ℝ))}

def spatialSupport (G : ReferenceJacobiCompactExtensionRoom F K) (i j : Fin 3) : Set R3 :=
  Prod.snd '' tsupport (G.scalar i j)

lemma spatialSupport_isCompact (G : ReferenceJacobiCompactExtensionRoom F K) (i j : Fin 3) :
    IsCompact (G.spatialSupport i j) :=
  (G.compactSupport i j).image continuous_snd

lemma scalar_zeroOutside (G : ReferenceJacobiCompactExtensionRoom F K) (i j : Fin 3) :
    ∀ p x, x ∉ G.spatialSupport i j → G.scalar i j (p,x)=0 := by
  intro p x hx
  by_contra hn
  exact hx ⟨(p,x),subset_tsupport (G.scalar i j) hn,rfl⟩

def jets (G : ReferenceJacobiCompactExtensionRoom F K) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    SmoothCoefficientJets 3 :=
  commonSupportCoefficientFamily 3 (G.scalar i j) (G.smooth i j) (G.spatialSupport i j)
    (G.spatialSupport_isCompact i j) (G.scalar_zeroOutside i j) p

lemma coefficientValue_jets (G : ReferenceJacobiCompactExtensionRoom F K) (i j : Fin 3)
    (p : ℝ × (R3 × ℝ)) : coefficientValue 3 (G.jets i j p) = fun x => G.scalar i j (p,x) := by
  funext x
  exact coefficientValue_commonSupportCoefficientFamily 3 (G.scalar i j) (G.smooth i j)
    (G.spatialSupport i j) (G.spatialSupport_isCompact i j) (G.scalar_zeroOutside i j) p x

lemma eventually_nativeThreeHalfCoefficientMulL_jets_eq
    (G : ReferenceJacobiCompactExtensionRoom F K)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ K) (i j : Fin 3) :
    ∀ᶠ t in 𝓝 p, nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (G.jets i j t) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j t) := by
  filter_upwards [G.sphereEq p hp i j] with t ht
  apply nativeThreeHalfCoefficientMulL_eq_of_sphereValue_eq hcalc hF hO hD τ0
  apply ContinuousMap.ext
  intro x
  change coefficientValue 3 (G.jets i j t) x.val = coefficientValue 3 (F i j t) x.val
  exact (congrFun (G.coefficientValue_jets i j t) x.val).trans (ht x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem exists_referenceJacobiCompactExtensionRoom
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K)
    (hInv : ∀ p ∈ K, ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    Nonempty (ReferenceJacobiCompactExtensionRoom
      (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K) := by
  classical
  have hExists (i j : Fin 3) :=
    exists_contDiff_compact_referenceJacobiBoundaryThreeHalfCoefficient_extension
      g hg L y0 Φ B ε C ρ H a w hData i j K hK hInv
  choose m hm hmc hEq using hExists
  exact ⟨⟨m,hm,hmc,fun p hp i j => hEq i j p hp⟩⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom.spatialSupport
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom.spatialSupport_isCompact
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom.scalar_zeroOutside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom.jets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom.coefficientValue_jets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ReferenceJacobiCompactExtensionRoom.eventually_nativeThreeHalfCoefficientMulL_jets_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceJacobiCompactExtensionRoom
