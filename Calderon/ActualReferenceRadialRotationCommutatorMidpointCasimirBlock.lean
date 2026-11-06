import Calderon.ActualReferenceUpperRotationCommutatorCasimirBlock
import Calderon.ActualReferenceRadialRotationCommutatorMidpointHarmonicBlock

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotationProjection

/-! Full upfront argument: EXPANSION-v005.json. All finite blocks use actual
physical coefficients and single injections. The second physical form term is retained;
no adjoint, symmetry, quantitative Sylvester bound or cutoff premise is assumed. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceSharpRadialHarmonicBlockL (p : ℝ × (R3 × ℝ)) (m n : ℕ) :
    harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m :=
  (sphereSobolevCoefficientL (1/2:ℝ) m).comp
    ((referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).comp (sphereSobolevSingleL (3/2:ℝ) n))

def referenceRadialRotationCommutatorMidpointHarmonicBlockL
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (m n : ℕ) :
    harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m :=
  (sphereSobolevCoefficientL 0 m).comp
    ((referenceRadialRotationCommutatorMidpointFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j p).comp (sphereSobolevSingleL 1 n))

lemma referenceRadialRotationCommutatorMidpoint_harmonic_casimir_block
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (m n : ℕ) (u : harmonicSphereSubspace n) :
    ((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)) •
      referenceSharpRadialHarmonicBlockL g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 p m n u =
    (-(1/2:ℝ)) • (∑ i : Fin 3, ∑ j : Fin 3,(
      harmonicSphereRotation m i j
        (referenceRadialRotationCommutatorMidpointHarmonicBlockL
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p m n u) +
      referenceRadialRotationCommutatorMidpointHarmonicBlockL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p m n
          (harmonicSphereRotation n i j u))) := by
  let K := referenceSharpRadialHarmonicBlockL g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 p m n
  let D := referenceRadialRotationCommutatorMidpointHarmonicBlockL
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hComm (i j : Fin 3) (v : harmonicSphereSubspace n) :
      D i j p m n v = harmonicSphereRotation m i j (K v) - K (harmonicSphereRotation n i j v) :=
    referenceRadialRotationCommutatorMidpointFamily_harmonic_block
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp m n v
  have hTerm (i j : Fin 3) :
      harmonicSphereRotation m i j (D i j p m n u) + D i j p m n (harmonicSphereRotation n i j u) =
      harmonicSphereRotation m i j (harmonicSphereRotation m i j (K u)) -
        K (harmonicSphereRotation n i j (harmonicSphereRotation n i j u)) := by
    rw [hComm,hComm,map_sub]
    abel
  have hSum : (∑ i : Fin 3, ∑ j : Fin 3,(
      harmonicSphereRotation m i j (D i j p m n u) + D i j p m n (harmonicSphereRotation n i j u))) =
      (-(2*((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)))) • K u := by
    simp_rw [hTerm,Finset.sum_sub_distrib]
    have hInner (i : Fin 3) :
        (∑ j : Fin 3, K (harmonicSphereRotation n i j (harmonicSphereRotation n i j u))) =
          K (∑ j : Fin 3, harmonicSphereRotation n i j (harmonicSphereRotation n i j u)) :=
      (map_sum K (fun j : Fin 3 =>
        harmonicSphereRotation n i j (harmonicSphereRotation n i j u)) Finset.univ).symm
    have hMapped :
        (∑ i : Fin 3, ∑ j : Fin 3,
          K (harmonicSphereRotation n i j (harmonicSphereRotation n i j u))) =
        K (∑ i : Fin 3, ∑ j : Fin 3,
          harmonicSphereRotation n i j (harmonicSphereRotation n i j u)) := by
      calc
        _ = ∑ i : Fin 3, K (∑ j : Fin 3,
            harmonicSphereRotation n i j (harmonicSphereRotation n i j u)) :=
          Finset.sum_congr rfl (fun i _ => hInner i)
        _ = _ := (map_sum K (fun i : Fin 3 => ∑ j : Fin 3,
          harmonicSphereRotation n i j (harmonicSphereRotation n i j u)) Finset.univ).symm
    have hLeft := sum_harmonicSphereRotation_twice m (K u)
    have hRight :
        (∑ i : Fin 3, ∑ j : Fin 3,
          K (harmonicSphereRotation n i j (harmonicSphereRotation n i j u))) =
        (-(2*(n:ℝ)*((n:ℝ)+1))) • K u :=
      hMapped.trans ((congrArg (fun z : harmonicSphereSubspace n => K z)
        (sum_harmonicSphereRotation_twice n u)).trans
          (K.map_smul (-(2*(n:ℝ)*((n:ℝ)+1))) u))
    calc
      _ = (-(2*(m:ℝ)*((m:ℝ)+1))) • K u -
          (-(2*(n:ℝ)*((n:ℝ)+1))) • K u :=
        congrArg₂ (fun x y : harmonicSphereSubspace m => x-y) hLeft hRight
      _ = (-(2*(m:ℝ)*((m:ℝ)+1)) - (-(2*(n:ℝ)*((n:ℝ)+1)))) • K u :=
        (sub_smul _ _ (K u)).symm
      _ = _ := congrArg (fun r : ℝ => r • K u) (by ring)
  change ((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)) • K u =
    (-(1/2:ℝ)) • (∑ i : Fin 3, ∑ j : Fin 3,(
      harmonicSphereRotation m i j (D i j p m n u) + D i j p m n (harmonicSphereRotation n i j u)))
  rw [hSum,smul_smul]
  congr 1
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialHarmonicBlockL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorMidpointHarmonicBlockL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorMidpoint_harmonic_casimir_block
