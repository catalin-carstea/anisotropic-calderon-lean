import Calderon.ActualHigherSFirstPhysicalCommutatorGraph
import Calderon.ActualFullEGainedBandGraph
import Calderon.FixedParameterProfileBudgets
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLeadingBracketGain

section Contraction
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
/-- Contract both original Q orders; neither Q symmetry nor operator commutation is used. -/
theorem firstFactor_contraction (X : Fin 3 → ℝ) (Q : Fin 3 → Fin 3 → ℝ) (E : Fin 3 → V) :
    (∑ m : Fin 3, X m • ((∑ j : Fin 3, Q m j • E j)+(∑ i : Fin 3, Q i m • E i))) =
      ∑ a : Fin 3, (∑ m : Fin 3, X m*(Q m a+Q a m)) • E a := by
  calc
    _ = ∑ m : Fin 3, ∑ a : Fin 3, (X m*(Q m a+Q a m)) • E a := by
      apply Finset.sum_congr rfl
      intro m _
      simp only [smul_add,Finset.smul_sum,smul_smul,mul_add,add_smul,Finset.sum_add_distrib]
    _ = ∑ a : Fin 3, ∑ m : Fin 3, (X m*(Q m a+Q a m)) • E a := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_smul]
end Contraction

section Graph
variable {U V N : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- Ordered compositions of two finite scalar-weighted operator sums. -/
theorem weighted_sums_comp_apply
    (A : Fin 3 → V →L[ℝ] N) (B : Fin 3 → U →L[ℝ] V)
    (a b : Fin 3 → ℝ) (s t : ℝ) (u : U) :
    (s • (∑ i : Fin 3, a i • A i)) ((t • (∑ j : Fin 3, b j • B j)) u) =
      ∑ i : Fin 3, ∑ j : Fin 3, ((s*t)*(a i*b j)) • A i (B j u) := by
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum]
  simp_rw [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun c : ℝ => c • A i (B j u)) (by ring)

/-- The true gained E/E graph transports the complete leading weighted bracket to the low endpoint. -/
theorem weighted_gain_graph
    (I : U →L[ℝ] V) (J : V →L[ℝ] N)
    (FH RH : Fin 3 → U →L[ℝ] V) (FL RL : Fin 3 → V →L[ℝ] N)
    (G : Fin 3 → Fin 3 → U →L[ℝ] V) (Glo : Fin 3 → Fin 3 → V →L[ℝ] N)
    (a b : Fin 3 → ℝ) (r : ℝ)
    (hG : ∀ i j : Fin 3, ∀ u : U, J (G i j u)=RL i (FH j u)-FL j (RH i u))
    (hGL : ∀ i j : Fin 3, (Glo i j).comp I=J.comp (G i j)) :
    ((-r^4) • (∑ i : Fin 3, ∑ j : Fin 3, (a i*b j) • Glo i j)).comp I =
      ((-r^2) • (∑ i : Fin 3, a i • RL i)).comp ((r^2) • (∑ j : Fin 3, b j • FH j))-
        ((r^2) • (∑ j : Fin 3, b j • FL j)).comp ((-r^2) • (∑ i : Fin 3, a i • RH i)) := by
  ext u
  have hGLu (i j : Fin 3) : Glo i j (I u)=J (G i j u) := by
    exact congrArg (fun T : U →L[ℝ] N => T u) (hGL i j)
  have h1 := weighted_sums_comp_apply RL FH a b (-r^2) (r^2) u
  rw [show (-r^2)*(r^2)= -r^4 by ring] at h1
  have h2 : (r^2 • (∑ j : Fin 3, b j • FL j)) ((-r^2 • (∑ i : Fin 3, a i • RH i)) u) =
      ∑ i : Fin 3, ∑ j : Fin 3, ((-r^4)*(a i*b j)) • FL j (RH i u) := by
    rw [weighted_sums_comp_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun c : ℝ => c • FL j (RH i u)) (by ring)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply]
  rw [h1,h2]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]
  simp_rw [hGLu,hG,Finset.smul_sum,smul_sub,smul_smul,Finset.sum_sub_distrib]
end Graph

open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)

/-- Both original Q orders in the actual first coordinate factor. -/
def firstCoordinateWeight (g g2 : MatrixField) (L : ℝ) (l a : Fin 3) (t : Tpar) : ℝ :=
  ∑ m : Fin 3, ActualBalancedFirstPrincipalError.frameEntry g L m l (t.1.1,t.1.2.1)*
    (referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 m a+
      referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 a m)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HF" => ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateFactor
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LF" => ActualHigherSFirstCoefficientJets.firstCoordinateFactor
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Exact original high first factor; all indices and both Q orders are retained. -/
theorem highFirstCoordinateFactor_eq_contracted (g2 : MatrixField) (l : Fin 3) (t : Tpar) :
    HF g2 l t = ∑ k : Fin 3, firstCoordinateWeight g g2 L l k t • EH k t := by
  exact firstFactor_contraction (V := Hi →L[ℝ] Half)
    (fun m => ActualBalancedFirstPrincipalError.frameEntry g L m l (t.1.1,t.1.2.1))
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 i j)
    (fun k => EH k t)

/-- Exact original low first factor with the same scalar coordinate weights. -/
theorem firstCoordinateFactor_eq_contracted (g2 : MatrixField) (l : Fin 3) (t : Tpar) :
    LF g2 l t = ∑ k : Fin 3, firstCoordinateWeight g g2 L l k t • EL k t := by
  exact firstFactor_contraction (V := Half →L[ℝ] Neg)
    (fun m => ActualBalancedFirstPrincipalError.frameEntry g L m l (t.1.1,t.1.2.1))
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 i j)
    (fun k => EL k t)

/-- Expected ordered leading reverse factor; extraction from the complete S-adjoint remains open. -/
def orderedReverseFirstCoordinateFactorHigh (g2 : MatrixField) (l : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  ∑ k : Fin 3, firstCoordinateWeight g g2 L l k t • eH k t

def orderedReverseFirstCoordinateFactorLow (g2 : MatrixField) (l : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  ∑ k : Fin 3, firstCoordinateWeight g g2 L l k t • eL k t

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  fullGainedHigh sphereSobolevInclusionL

/-- Exact actual E/E graph specialization of the leading weighted bracket.
The actual endpoint producer must supply these graph facts; no self-form bound or S-adjoint extraction is asserted. -/
theorem actual_first_weighted_gain_graph
    (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
    (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg) (t : Tpar)
    (hG : ∀ i j : Fin 3, ∀ u : Hi,
      JL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t u)=
        eL i t (EH j t u)-EL j t (eH i t u))
    (hCl : ∀ i j : Fin 3, (Cl i j t).comp IH= (JL).comp
      (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t))
    (g2 : MatrixField) (l k : Fin 3) (r : ℝ) :
    ((-r^4) • (∑ i : Fin 3, ∑ j : Fin 3,
      (firstCoordinateWeight g g2 L l i t*firstCoordinateWeight g g2 L k j t) • Cl i j t)).comp IH =
      ((-r^2) • orderedReverseFirstCoordinateFactorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l t).comp
        ((r^2) • HF g2 k t)-
      ((r^2) • LF g2 k t).comp
        ((-r^2) • orderedReverseFirstCoordinateFactorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l t) := by
  have Hgain := weighted_gain_graph (U := Hi) (V := Half) (N := Neg) IH JL (fun i => EH i t) (fun i => eH i t)
    (fun i => EL i t) (fun i => eL i t)
    (fun i j => fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t)
    (fun i j => Cl i j t) (fun i => firstCoordinateWeight g g2 L l i t)
    (fun j => firstCoordinateWeight g g2 L k j t) r hG hCl
  let BRL := orderedReverseFirstCoordinateFactorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l t
  let BRH := orderedReverseFirstCoordinateFactorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l t
  have hFactors := congrArg₂
    (fun (X : Hi →L[ℝ] Half) (Y : Half →L[ℝ] Neg) =>
      ((-r^2) • BRL).comp ((r^2) • X)-((r^2) • Y).comp ((-r^2) • BRH))
    (highFirstCoordinateFactor_eq_contracted g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k t).symm
    (firstCoordinateFactor_eq_contracted g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k t).symm
  dsimp only [BRL,BRH,orderedReverseFirstCoordinateFactorLow,
    orderedReverseFirstCoordinateFactorHigh] at hFactors
  exact Hgain.trans hFactors

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLeadingBracketGain
