import Calderon.ActualReferenceWeakHalfLift
import Calderon.ActualReferenceStrongRoom
import Calderon.OrdinaryWeightedDriftEnergy
import Calderon.NativeHarmonicLiftOrderCoherence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceOrdinaryStrongDriftFamily_energy_of_elliptic
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam) (E : BallSobolev (s+2)) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E)) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun z => a ((q,p),z))
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
        (TauCeti.Wkp.firstOrder (s+1) E) (v : BallH1) := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  let F : SmoothCoefficientMatrix (s+2) := commonSupportMatrixFamily (s+2)
    (jointFixedParameterSlice a q) h.1 (closedBall (0:R3) 3) (isCompact_closedBall _ _)
    h.2.2.2.1 p
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s+2) F) lam Lam := by
    change TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s+2) (commonSupportMatrixFamily (s+2)
        (jointFixedParameterSlice a q) h.1 (closedBall (0:R3) 3) (isCompact_closedBall _ _)
        h.2.2.2.1 p)) lam Lam
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hUE
  have hc := memLp_coefficientMatrixEnergyIntegrand (s+2) F hUEF
  have he := ordinaryStrongDriftFamily_energy hcalc s
    (jointFixedParameterSlice a q) h.1 (jointFixedParameterSlice w q) h.2.1
    (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
    (closedBall (0:R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p hc E v
  rw [weightedDriftSlice_reference_eq g L y0 Φ B ε C ρ H a w hData q p] at he
  exact he

lemma referenceHarmonicLiftFamily_weak_energy
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).IsInvertible)
    (E : BallSobolev (s+2)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (TauCeti.Wkp.firstOrder (s+1)
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E)) (v : BallH1) = 0 := by
  have he := referenceOrdinaryStrongDriftFamily_energy_of_elliptic
    g L y0 Φ B ε C ρ H a w hData hcalc s q p lam Lam hUE
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E) v
  have hk : referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E) = 0 :=
    guardedHarmonicLiftFamily_kernel _ _ _ p hi rfl E
  rw [hk] at he
  have hz : TauCeti.Wkp.value (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) s 0 = 0 :=
    (TauCeti.Wkp.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s).map_zero
  rw [hz,TauCeti.PDE.dirichletForcing_apply,inner_zero_left] at he
  exact he.symm

lemma referenceHarmonicLiftFamily_boundary_difference
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (p : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).IsInvertible)
    (E : BallSobolev (s+2)) :
    TauCeti.Wkp.firstOrder (s+1)
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E-E) ∈
        TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let c : StrongDirichletSpace s :=
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).inverse
      (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E)
  have he : referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E =
      E-(c : BallSobolev (s+2)) := by
    change guardedHarmonicLiftFamily _ _ _ p E = _
    rw [guardedHarmonicLiftFamily_eq _ _ _ p hi,harmonicLiftL_apply]
    rfl
  have hm : referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E-E ∈
      strongDirichletSubmodule s := by
    have he' : E-(c : BallSobolev (s+2))-E = -(c : BallSobolev (s+2)) := by abel
    rw [he,he']
    exact (strongDirichletSubmodule s).neg_mem c.property
  exact (mem_strongDirichletSubmodule s _).mp hm

lemma firstOrder_referenceHarmonicLiftFamily_eq_weakHalfLift
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (hs : UnitBallSmallDriftData (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) lam)
    (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrderL 1
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
        (harmonicLiftCompletion hF f)) =
      referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  have hi := referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q p lam Lam hUE hs.1
  apply eq_referenceWeakHalfLiftFamily_of_weak_energy
    g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p) lam hs
  · have hd := referenceHarmonicLiftFamily_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc 0 q p hi (harmonicLiftCompletion hF f)
    have hd' : TauCeti.Wkp.firstOrderL 1
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
          (harmonicLiftCompletion hF f)) - TauCeti.Wkp.firstOrderL 1 (harmonicLiftCompletion hF f) ∈
          TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
      rw [← map_sub]
      exact hd
    have hn := (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).neg_mem hd'
    rw [neg_sub,firstOrder_harmonicLiftCompletion hF hO] at hn
    exact hn
  · intro v
    exact referenceHarmonicLiftFamily_weak_energy
      g L y0 Φ B ε C ρ H a w hData hcalc 0 q p lam Lam hUE hi (harmonicLiftCompletion hF f) v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
