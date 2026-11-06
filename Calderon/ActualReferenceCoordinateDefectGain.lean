import Calderon.ActualReferenceCoordinateForcingFamily
import Calderon.ActualReferenceCoordinateDefectClosure
import Calderon.ActualReferenceInvertibleStrongForcing
import Calderon.ActualReferenceOrthogonalWeakData

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHalfSmoothMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceWeakHalfLiftFamily_weak_energy_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (v : BallH1) = 0 := by
  let hcoeff := referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p
  have hi : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => a (p,x)) (b := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      (c := 0) hcoeff).IsInvertible :=
    referenceNativeEnergy_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc p hWeak
  have hW := congrArg (fun W : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 => W f)
    (referenceWeakHalfLiftFamily_eq_nativeWeakHalfLift g L y0 Φ B ε C ρ H a w hData hcalc hF p hcoeff)
  have hEnergy := congrArg (fun u : BallH1 => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 u (v : BallH1)) hW
  exact hEnergy.trans (nativeWeakHalfLift_weak_solution (fun x => a (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hcoeff hF hi f v)

theorem referenceCoordinateWeakDefectFamily_energy
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ))
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
      (referenceCoordinateWeakDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k hM hm hg p f)
      (v : BallH1) =
    ⟪referenceCoordinateCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc k p
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f),
      TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
  let W : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 := referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
  let T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfSmoothMulL hF hO hD τ0 (coordinateSmoothDatum k) hM hm hg
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg
  have hSv : S (v : BallH1) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    dsimp only [S]
    rw [TauCeti.W1p.contDiffSMulL_apply]
    exact TauCeti.W1p.contDiffSMul_mem_w1p0Submodule (coordinateSmoothDatum k).2 hM hm hg v.property
  have hu := referenceWeakHalfLiftFamily_weak_energy_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hWeak f ⟨S (v : BallH1),hSv⟩
  have hu' := referenceWeakHalfLiftFamily_weak_energy_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hWeak (T f) v
  have hcancel := referenceEnergy_coordinate_product_difference_forcing
    g L y0 Φ B ε C ρ H a w hData hcalc p k hM hm hg (W f) v
  let E : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero := referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  have hsub : E (W (T f)-S (W f)) v = E (W (T f)) v-E (S (W f)) v :=
    congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) (map_sub E (W (T f)) (S (W f)))
  have hval (u : BallH1) : E u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 u (v : BallH1) :=
    referenceWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u v
  simp only [hval] at hsub
  rw [referenceCoordinateWeakDefectFamily_apply]
  change TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
    (W (T f)-S (W f)) (v : BallH1) = _
  linarith

def referenceCoordinateStrongDefectFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (k : Fin 3) (p : ℝ × (R3 × ℝ)) : SphereSobolev (1/2 : ℝ) →L[ℝ] BallSobolev 2 :=
  (strongDirichletSubmodule 0).toSubmodule.subtypeL.comp
    ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).inverse.comp
      ((referenceCoordinateCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc k p).comp
        (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)))

theorem firstOrder_referenceCoordinateStrongDefectFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) :
    TauCeti.Wkp.firstOrder 1
      (referenceCoordinateStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF k p f) =
    referenceCoordinateWeakDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k hM hm hg p f := by
  let U : BallH1Zero :=
    ⟨referenceCoordinateWeakDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k hM hm hg p f,
      referenceCoordinateWeakDefectFamily_mem_zero g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 k hM hm hg p f⟩
  let Q : BallSobolev 0 :=
    referenceCoordinateCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc k p
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
  have hU := eq_referenceStrongDriftFamily_inverse_projection_of_weak_forcing
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 p.1 p.2 hStrong hWeak Q U
    (fun v => referenceCoordinateWeakDefectFamily_energy g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 k hM hm hg p hWeak f v)
  have hv := congrArg (fun u : BallH1Zero => (u : BallH1)) hU
  exact hv.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
