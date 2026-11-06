import Calderon.ActualTZeroNegativeProfileCap
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualHigherSScalarCommutatorNativeForm

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroECommutators
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ReferenceDensityBounds AmbientReferenceRaising ConformalDepth SmoothMetricFrame MovingFrameConnection
  ActualHigherSFormation ActualHigherSScalarCommutatorNativeForm

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete


section ReferenceFactors
variable (g : MatrixField) (L q dr Ar : ℝ) (p : ℕ)

/-- Literal reference connection and original log-radius coefficients. -/
def referenceAngularZeroCoefficient (x : R3) (i : Fin 3) : Generator → ℝ
  | Sum.inl ab => (1/2 : ℝ)*referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) ab.1 ab.2
  | Sum.inr _ => referenceFrameDerivative g L q i
      (fun y => Real.log (referenceRadius dr Ar p L y)) x

local notation "cc" => referenceAngularZeroCoefficient g L q dr Ar p

def referenceAngularHigh (x : R3) (i : Fin 3) : Hi →L[ℝ] Half :=
  ∑ V : Generator, cc x i V • generatorHigh V

def referenceAngularLow (x : R3) (i : Fin 3) : Half →L[ℝ] Neg :=
  ∑ V : Generator, cc x i V • generatorLow V

/-- Sharp weighted angular factor; raw Tdag zero ALSO retains its separate -fi IH. -/
def referenceAngularSharpHigh (x : R3) (i : Fin 3) : Hi →L[ℝ] Half :=
  ∑ V : Generator, cc x i V • generatorSharpHigh V

def referenceAngularSharpLow (x : R3) (i : Fin 3) : Half →L[ℝ] Neg :=
  ∑ V : Generator, cc x i V • generatorSharpLow V

theorem referenceAngularHigh_eq (x : R3) (i : Fin 3) :
    referenceAngularHigh g L q dr Ar p x i =
      referenceHighHorizontalAngularL g L q x i+
        referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x •
          sphereSobolevShiftedDegreeL (3/2 : ℝ) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceAngularHigh,referenceAngularZeroCoefficient,generatorHigh,
    referenceHighHorizontalAngularL,_root_.sum_apply,_root_.smul_apply,_root_.add_apply,_root_.neg_apply]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,
    _root_.sum_apply,_root_.smul_apply,_root_.add_apply,_root_.neg_apply,
    Finset.smul_sum,smul_smul,smul_neg,Finset.sum_neg_distrib]

theorem referenceAngularLow_eq (x : R3) (i : Fin 3) :
    referenceAngularLow g L q dr Ar p x i =
      referenceLowerHorizontalAngularL g L q x i+
        referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x •
          sphereSobolevShiftedDegreeL (1/2 : ℝ) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceAngularLow,referenceAngularZeroCoefficient,generatorLow,
    referenceLowerHorizontalAngularL,_root_.sum_apply,_root_.smul_apply,_root_.add_apply,_root_.neg_apply]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,
    _root_.sum_apply,_root_.smul_apply,_root_.add_apply,_root_.neg_apply,
    Finset.smul_sum,smul_smul,smul_neg,Finset.sum_neg_distrib]

theorem referenceAngularSharpHigh_eq (x : R3) (i : Fin 3) :
    referenceAngularSharpHigh g L q dr Ar p x i =
      -referenceHighHorizontalAngularL g L q x i+
        referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x •
          sphereSobolevShiftedDegreeL (3/2 : ℝ) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceAngularSharpHigh,referenceAngularZeroCoefficient,generatorSharpHigh,generatorHigh,
    referenceHighHorizontalAngularL,_root_.sum_apply,_root_.smul_apply,_root_.add_apply,_root_.neg_apply]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,
    _root_.sum_apply,_root_.smul_apply,_root_.add_apply,_root_.neg_apply,
    Finset.smul_sum,smul_smul,smul_neg,Finset.sum_neg_distrib]

theorem referenceAngularSharpLow_eq (x : R3) (i : Fin 3) :
    referenceAngularSharpLow g L q dr Ar p x i =
      -referenceLowerHorizontalAngularL g L q x i+
        referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x •
          sphereSobolevShiftedDegreeL (1/2 : ℝ) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceAngularSharpLow,referenceAngularZeroCoefficient,generatorSharpLow,generatorLow,
    referenceLowerHorizontalAngularL,_root_.sum_apply,_root_.smul_apply,_root_.add_apply,_root_.neg_apply]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,
    _root_.sum_apply,_root_.smul_apply,_root_.add_apply,_root_.neg_apply,
    Finset.smul_sum,smul_smul,smul_neg,Finset.sum_neg_distrib]
end ReferenceFactors

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GenRoom" => GeneratorEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" => higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CH" => pairedLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DH" => pairedRightHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "cc" => referenceAngularZeroCoefficient g L

def referenceLeftHigh (hreg : FixedDirichletRegularity) (d0 : ℝ) (germs : CoeffRoom d0)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (i j : Fin 3) : Hi →L[ℝ] Half :=
  ∑ V : Generator, cc q dr Ar p x i V • CH hreg d0 germs V j ((Tq dr Ar p q) x)

def referenceRightHigh (hreg : FixedDirichletRegularity) (d0 : ℝ) (germs : CoeffRoom d0)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (i j : Fin 3) : Hi →L[ℝ] Half :=
  ∑ V : Generator, cc q dr Ar p x i V • DH hreg d0 germs V j ((Tq dr Ar p q) x)

def referenceLeftLow (hreg : FixedDirichletRegularity) (d0 : ℝ) (germs : CoeffRoom d0)
    (d : ℝ) (room : GenRoom hreg d0 germs d)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (i j : Fin 3) : Half →L[ℝ] Neg :=
  ∑ V : Generator, cc q dr Ar p x i V • room.low V j ((Tq dr Ar p q) x)

local notation "LC" => referenceLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RC" => referenceRightHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LL" => referenceLeftLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow reverseEHigh reverseELow
  pairedLeftHigh pairedRightHigh generatorHigh generatorLow generatorSharpHigh generatorSharpLow
  sphereSobolevInclusionL sphereSobolevRotationL sphereSobolevShiftedDegreeL

theorem reference_left_graph (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (d : ℝ) (room : GenRoom hreg d0 germs d)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (i j : Fin 3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom d) (u : Hi) :
    JL (LC hreg d0 germs dr Ar p q x i j u) =
      referenceAngularSharpLow g L q dr Ar p x i (EH j ((Tq dr Ar p q) x) u)-
        EL j ((Tq dr Ar p q) x) (referenceAngularSharpHigh g L q dr Ar p x i u) := by
  have h (V : Generator) := room.highGraph V j _ hx u
  simp only [referenceLeftHigh,referenceAngularSharpLow,referenceAngularSharpHigh,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  simp_rw [h]
  simp only [smul_sub,Finset.sum_sub_distrib]

theorem reference_right_graph (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (d : ℝ) (room : GenRoom hreg d0 germs d)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (i j : Fin 3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom d) (u : Hi) :
    JL (RC hreg d0 germs dr Ar p q x i j u) =
      eL j ((Tq dr Ar p q) x) (referenceAngularHigh g L q dr Ar p x i u)-
        referenceAngularLow g L q dr Ar p x i (eH j ((Tq dr Ar p q) x) u) := by
  have h (V : Generator) := room.partnerGraph V j _ hx u
  simp only [referenceRightHigh,referenceAngularHigh,referenceAngularLow,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  simp_rw [h]
  simp only [smul_sub,Finset.sum_sub_distrib]

theorem reference_upper_graph (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (d : ℝ) (room : GenRoom hreg d0 germs d)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (i j : Fin 3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom d) :
    (LL hreg d0 germs d room dr Ar p q x i j).comp IH =
      (JL).comp (LC hreg d0 germs dr Ar p q x i j) := by
  apply ContinuousLinearMap.ext
  intro u
  have h (V : Generator) :
      room.low V j ((Tq dr Ar p q) x) (IH u)=JL (CH hreg d0 germs V j ((Tq dr Ar p q) x) u) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A u) (room.upper V j _ hx)
  simp only [referenceLeftLow,referenceLeftHigh,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul,h]

theorem reference_adjunction (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (d : ℝ) (room : GenRoom hreg d0 germs d)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (i j : Fin 3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom d) (u v : Hi) :
    PP (IH v) (JL (LC hreg d0 germs dr Ar p q x i j u)) =
      PP (IH u) (JL (RC hreg d0 germs dr Ar p q x i j v)) := by
  simp only [← halfDualPairingL_apply,referenceLeftHigh,referenceRightHigh,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro V _
  simpa only [halfDualPairingL_apply] using congrArg
    (fun z : ℝ => cc q dr Ar p x i V • z) (room.adjunction V j _ hx u v)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroECommutators

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroECommutators.reference_left_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroECommutators.reference_right_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroECommutators.reference_upper_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReferenceZeroECommutators.reference_adjunction
