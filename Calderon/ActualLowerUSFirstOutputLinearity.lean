import Calderon.ActualLowerUSZeroAngularLocality
import Calderon.ActualLowerUSFirstOutput
import Calderon.ActualFiniteHarmonicModelScalarExpansion

/-! Global genuine first-output finite linearity and angular scalar centrality.
No room hypothesis and no output finiteness assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFirstOutput
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation ActualHigherSFirstPhysicalCommutatorGraph

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q


variable (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3)
local notation "Pout" => nativeFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  g2 dr Ar p q j

lemma nativeFirstOut_add (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    Pout (F+G) x = Pout F x+Pout G x := by
  unfold nativeFirstOut finiteCoreSobolevLift
  simp only [map_add,Submodule.coe_add,Pi.add_apply]

lemma nativeFirstOut_smul (r : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    Pout (r • F) x = r • Pout F x := by
  unfold nativeFirstOut finiteCoreSobolevLift
  simp only [map_smul,Submodule.coe_smul,Pi.smul_apply]

lemma nativeFirstOut_sum {ι : Type*} [Fintype ι]
    (F : ι → smoothCompactFiniteSphereCore hO hD) (x : R3) :
    Pout (∑ i, F i) x = ∑ i, Pout (F i) x := by
  unfold nativeFirstOut finiteCoreSobolevLift
  simp only [map_sum,Submodule.coe_sum,Finset.sum_apply]

lemma nativeFirstOut_coreScalar (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    Pout (coreScalar hO hD c hc F) x = c x • Pout F x := by
  unfold nativeFirstOut
  rw [ActualLowerUSZeroAngularLocality.finiteCoreSobolevLift_coreScalar]
  simp only [map_smul]

lemma nativeFirstOut_coreScalarCombination {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    Pout (coreScalarCombination hO hD T c hc F) x = ∑ i, c i x • Pout (T i F) x := by
  simp only [coreScalarCombination,LinearMap.sum_apply,Module.End.mul_apply]
  rw [nativeFirstOut_sum]
  simp only [nativeFirstOut_coreScalar]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFirstOutput
