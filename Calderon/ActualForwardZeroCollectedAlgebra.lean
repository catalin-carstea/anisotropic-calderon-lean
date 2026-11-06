import Calderon.ActualHigherSCoefficientExtraction
import Calderon.ActualZeroCoefficientLinearity
import Calderon.ClmInheritedStructureData

/-! Native forward collected-zero algebra on opaque Sobolev CLMs only, with no physical
endpoint or profile context. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualForwardZeroCollectedAlgebra
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local irreducible] ActualHigherSCoefficientExtraction.zeroCoefficient

theorem native_forward_collected_zero
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b f : Fin 3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (E : Fin 3 → Hi →L[ℝ] Half) (D : Fin 3 → Fin 3 → Hi →L[ℝ] Half)
    (T : Fin 3 → Fin 3 → Hi →L[ℝ] Neg)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half) :
    ActualHigherSCoefficientExtraction.zeroCoefficient r Q b
      (fun i j => (JL).comp (D i j)+T i j+f i • (JL).comp (E j)-
        ∑ k : Fin 3, Gamma i k j • (JL).comp (E k)) E El Alo Ahi =
    ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • T i j)+
      r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((Alo i).comp (E j)+(El i).comp (Ahi j))))+
      r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El i).comp (E j)))+
      (JL).comp (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
        (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k))+
        r^2 • (∑ i : Fin 3, b i • E i)) := by
  let Ra : Hi →L[ℝ] Neg := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
    ((Alo i).comp (E j)+(El i).comp (Ahi j)))
  let Rs : Hi →L[ℝ] Neg := r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El i).comp (E j))
  have hSplit0 := ActualZeroCoefficientLinearity.forward_zero_split (V := Hi) (H := Half) (N := Neg)
  try simp only [clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hSplit0
  have hSplit := hSplit0 JL r Q b f Gamma E D T Ra Rs
  unfold ActualHigherSCoefficientExtraction.zeroCoefficient
  exact hSplit
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualForwardZeroCollectedAlgebra
