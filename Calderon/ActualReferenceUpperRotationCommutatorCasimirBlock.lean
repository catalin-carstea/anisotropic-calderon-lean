import Calderon.ActualReferenceUpperRotationCommutatorHarmonicBlock
import Calderon.HarmonicSphereRotationCasimirVector

set_option autoImplicit false
noncomputable section
open Set MeasureTheory MvPolynomial
open scoped InnerProductSpace ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotationProjection
  SpectralWeightedGraph AngularPolynomial RotationCasimir

/-! Full upfront argument: EXPANSION-v005.json. These are actual physical finite
harmonic blocks, with all9 ordered rotations and exact negative-half Casimir factor.
Degree zero is retained; no uniform form/adjoint premise is introduced. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceSharpRadialRotationCommutatorL_harmonic_casimir_block
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (m n : ℕ) (u : harmonicSphereSubspace n) :
    ((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)) •
      sphereSobolevCoefficientL (1/2:ℝ) m
        (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 p (sphereSobolevSingleL (3/2:ℝ) n u)) =
    (-(1/2:ℝ)) • (∑ i : Fin 3, ∑ j : Fin 3,(
      harmonicSphereRotation m i j
        (sphereSobolevCoefficientL (1/2:ℝ) m
          (referenceSharpRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData
            hcalc hF hO hD τ0 i j p (sphereSobolevSingleL (3/2:ℝ) n u))) +
      sphereSobolevCoefficientL (1/2:ℝ) m
        (referenceSharpRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 i j p
            (sphereSobolevSingleL (3/2:ℝ) n (harmonicSphereRotation n i j u))))) := by
  let K : harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m :=
    (sphereSobolevCoefficientL (1/2:ℝ) m).comp
      ((referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 p).comp (sphereSobolevSingleL (3/2:ℝ) n))
  let D (i j : Fin 3) : harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m :=
    (sphereSobolevCoefficientL (1/2:ℝ) m).comp
      ((referenceSharpRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j p).comp (sphereSobolevSingleL (3/2:ℝ) n))
  have hComm (i j : Fin 3) (v : harmonicSphereSubspace n) :
      D i j v = harmonicSphereRotation m i j (K v) - K (harmonicSphereRotation n i j v) :=
    referenceSharpRadialRotationCommutatorL_harmonic_block
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak m n v
  have hTerm (i j : Fin 3) :
      harmonicSphereRotation m i j (D i j u) + D i j (harmonicSphereRotation n i j u) =
      harmonicSphereRotation m i j (harmonicSphereRotation m i j (K u)) -
        K (harmonicSphereRotation n i j (harmonicSphereRotation n i j u)) := by
    rw [hComm,hComm,map_sub]
    abel
  have hSum : (∑ i : Fin 3, ∑ j : Fin 3,(
      harmonicSphereRotation m i j (D i j u) + D i j (harmonicSphereRotation n i j u))) =
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
      harmonicSphereRotation m i j (D i j u) + D i j (harmonicSphereRotation n i j u)))
  rw [hSum,smul_smul]
  congr 1
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialRotationCommutatorL_harmonic_casimir_block
