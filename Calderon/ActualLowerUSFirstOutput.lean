import Calderon.ActualHigherSFirstPhysicalCommutatorGraph

/-! A single public construction of the genuine physical first-coordinate P_j,
without output finiteness or analytic hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFirstOutput
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation ActualHigherSFirstPhysicalCommutatorGraph
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

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

/-- Genuine full physical first-coordinate coefficient applied to the exact
finite high input; the resulting physical output need not be angularly finite. -/
def nativeFirstOut (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (j : Fin 3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  sphereSobolevHalfToSphereL2L hO hD
    (highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q x j (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x))

/-- Original native high/negative graph, retaining the same common formation
room and selected canonical first coefficient. -/
theorem nativeFirstOut_negative_graph
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom δ) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (nativeFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          g2 dr Ar p q j F x)) =
    ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q x j (finiteCoreSobolevLift hO hD (1/2 : ℝ) F x) := by
  unfold nativeFirstOut
  rw [sphereSobolevHalfToSphereL2L_negative_compatibility]
  rw [highFirstCoordinateCoefficient_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm g2 dr Ar p q j x hx]
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFirstOutput
