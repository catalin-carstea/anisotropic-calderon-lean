import Calderon.ActualReferenceGaugeBoundaryCoefficientFamilies
import Calderon.SmoothSignedTaylorRemainder

/-! Tangent radial remainder. Actual ambient Taylor subtractions are retained; the
zero/first radial cancellation is used only on the sphere. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)

def referenceGaugeTangentRadialFamily (j : Fin 3)
    (p : ((ℝ × R3) × R3) × ℝ) : ℝ :=
  referenceGaugeTangentCoefficient g L Φ a j ((p.1.1.1,(p.1.1.2,p.2)),p.1.2)

def referenceGaugeTangentSecondRemainder (j : Fin 3)
    (p : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  secondTaylorRemainder
    (fun t : ℝ => referenceGaugeTangentCoefficient g L Φ a j
      ((p.1.1,(p.1.2.1,t)),p.2)) p.1.2.2

variable (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

include hData hg

theorem contDiff_referenceGaugeTangentRadialFamily (j : Fin 3) :
    ContDiff ℝ ∞ (referenceGaugeTangentRadialFamily g L Φ a j) :=
  (contDiff_referenceGaugeTangentCoefficient g L Φ y0 B ε C ρ H a w hData hg j).comp
    ((contDiff_fst.fst.fst.prodMk (contDiff_fst.fst.snd.prodMk contDiff_snd)).prodMk
      contDiff_fst.snd)

attribute [local irreducible] referenceGaugeTangentRadialFamily
  referenceGaugeTangentSecondRemainder secondTaylorRemainder

theorem contDiff_referenceGaugeTangentSecondRemainder (j : Fin 3) :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondRemainder g L Φ a j) := by
  unfold referenceGaugeTangentSecondRemainder
  have hR := contDiff_secondTaylorRemainder_joint
    (referenceGaugeTangentRadialFamily g L Φ a j)
    (contDiff_referenceGaugeTangentRadialFamily g L Φ a y0 B ε C ρ H w hData hg j)
  have hPerm : ContDiff ℝ ∞ (fun p : (ℝ × (R3 × ℝ)) × R3 =>
      (((p.1.1,p.1.2.1),p.2),p.1.2.2)) :=
    (((contDiff_fst.fst.prodMk contDiff_fst.snd.fst).prodMk contDiff_snd).prodMk
      contDiff_fst.snd.snd)
  simpa only [referenceGaugeTangentRadialFamily,Function.comp_def] using hR.comp hPerm

omit hg in
theorem referenceGaugeTangentSecondRemainder_support
    (j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) (hz : z ∉ closedBall (0 : R3) 3) :
    referenceGaugeTangentSecondRemainder g L Φ a j (p,z) = 0 := by
  have hZero : (fun t : ℝ => referenceGaugeTangentCoefficient g L Φ a j
      ((p.1,(p.2.1,t)),z)) = fun _ : ℝ => 0 := by
    funext t
    exact referenceGaugeTangentCoefficient_support g L Φ y0 B ε C ρ H a w hData
      j (p.1,(p.2.1,t)) z hz
  unfold referenceGaugeTangentSecondRemainder
  rw [hZero]
  simp [secondTaylorRemainder]

theorem referenceGaugeTangentCoefficient_radial_taylor
    (j : Fin 3) (q : ℝ) (y : R3) (r : ℝ) (z : R3) :
    referenceGaugeTangentCoefficient g L Φ a j ((q,(y,r)),z) =
      referenceGaugeTangentCoefficient g L Φ a j ((q,(y,0)),z) +
      r * deriv (fun t : ℝ => referenceGaugeTangentCoefficient g L Φ a j ((q,(y,t)),z)) 0 +
      r^2 * referenceGaugeTangentSecondRemainder g L Φ a j ((q,(y,r)),z) := by
  have hSlice : ContDiff ℝ ∞
      (fun t : ℝ => referenceGaugeTangentCoefficient g L Φ a j ((q,(y,t)),z)) :=
    (contDiff_referenceGaugeTangentCoefficient g L Φ y0 B ε C ρ H a w hData hg j).comp
      ((contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).prodMk contDiff_const)
  simpa only [referenceGaugeTangentSecondRemainder,smul_eq_mul] using
    signed_taylor_integral_remainder
      (fun t : ℝ => referenceGaugeTangentCoefficient g L Φ a j ((q,(y,t)),z)) r
      (fun t ht => hSlice.contDiffAt)

theorem referenceGaugeTangentCoefficient_eq_radius_sq_mul_secondRemainder_on_sphere
    (j : Fin 3) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) (r : ℝ) (x : UnitSphere) :
    referenceGaugeTangentCoefficient g L Φ a j ((q,(y,r)),x.val) =
      r^2 * referenceGaugeTangentSecondRemainder g L Φ a j ((q,(y,r)),x.val) := by
  obtain ⟨hZero,hFirst⟩ := referenceGaugeTangentCoefficient_zero_radial_jet
    g L Φ y0 B ε C ρ H a w hData q hq y hy x j
  have hTaylor := referenceGaugeTangentCoefficient_radial_taylor
    g L Φ a y0 B ε C ρ H w hData hg j q y r x.val
  simpa only [hZero,hFirst.deriv,mul_zero,zero_add] using hTaylor

def referenceGaugeTangentSecondRemainderJetsFamily (n : ℕ) (j : Fin 3) :
    (ℝ × (R3 × ℝ)) → SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (referenceGaugeTangentSecondRemainder g L Φ a j)
    (contDiff_referenceGaugeTangentSecondRemainder g L Φ a y0 B ε C ρ H w hData hg j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRemainder_support g L Φ a y0 B ε C ρ H w hData j)

theorem coefficientValue_referenceGaugeTangentSecondRemainderJetsFamily
    (n : ℕ) (j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) :
    coefficientValue n (referenceGaugeTangentSecondRemainderJetsFamily
      g L Φ a y0 B ε C ρ H w hData hg n j p) z =
      referenceGaugeTangentSecondRemainder g L Φ a j (p,z) :=
  coefficientValue_commonSupportCoefficientFamily n (referenceGaugeTangentSecondRemainder g L Φ a j)
    (contDiff_referenceGaugeTangentSecondRemainder g L Φ a y0 B ε C ρ H w hData hg j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRemainder_support g L Φ a y0 B ε C ρ H w hData j) p z

theorem referenceGaugeTangentSecondRemainderJetsFamily_jet
    (n : ℕ) (j : Fin 3) (p : ℝ × (R3 × ℝ)) (k : Fin (n+1)) (z : R3) :
    (referenceGaugeTangentSecondRemainderJetsFamily
      g L Φ a y0 B ε C ρ H w hData hg n j p).1 k z =
      iteratedFDeriv ℝ k.val (fun x => referenceGaugeTangentSecondRemainder g L Φ a j (p,x)) z :=
  commonSupportCoefficientFamily_jet n (referenceGaugeTangentSecondRemainder g L Φ a j)
    (contDiff_referenceGaugeTangentSecondRemainder g L Φ a y0 B ε C ρ H w hData hg j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRemainder_support g L Φ a y0 B ε C ρ H w hData j) p k z

theorem contDiff_referenceGaugeTangentSecondRemainderJetsFamily_val
    (n : ℕ) (j : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (referenceGaugeTangentSecondRemainderJetsFamily
        g L Φ a y0 B ε C ρ H w hData hg n j p).1) :=
  contDiff_commonSupportCoefficientFamily_val n (referenceGaugeTangentSecondRemainder g L Φ a j)
    (contDiff_referenceGaugeTangentSecondRemainder g L Φ a y0 B ε C ρ H w hData hg j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRemainder_support g L Φ a y0 B ε C ρ H w hData j)

theorem exists_compact_referenceGaugeTangentSecondRemainderJetsFamily_parameter_jets
    (n : ℕ) (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) :
    ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ j : Fin 3, ∀ k : ℕ, k ≤ N → ∀ p ∈ Q,
      ‖iteratedFDeriv ℝ k (fun t : ℝ × (R3 × ℝ) =>
        (referenceGaugeTangentSecondRemainderJetsFamily
          g L Φ a y0 B ε C ρ H w hData hg n j t).1) p‖ ≤ M := by
  intro N
  have hEach (j : Fin 3) := exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentSecondRemainderJetsFamily_val
      g L Φ a y0 B ε C ρ H w hData hg n j) Q hQ N
  choose M hM hBound using hEach
  refine ⟨∑ j : Fin 3, M j,Finset.sum_nonneg (fun j hj => hM j),?_⟩
  intro j k hk p hp
  exact (hBound j k hk p hp).trans
    (Finset.single_le_sum (fun l hl => hM l) (Finset.mem_univ j))

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentRadialFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentSecondRemainder
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeTangentRadialFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeTangentSecondRemainder
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentSecondRemainder_support
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentCoefficient_radial_taylor
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentCoefficient_eq_radius_sq_mul_secondRemainder_on_sphere
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentSecondRemainderJetsFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.coefficientValue_referenceGaugeTangentSecondRemainderJetsFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeTangentSecondRemainderJetsFamily_jet
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeTangentSecondRemainderJetsFamily_val
#print axioms OAI.AnisotropicCalderon.ConnectionError.exists_compact_referenceGaugeTangentSecondRemainderJetsFamily_parameter_jets
