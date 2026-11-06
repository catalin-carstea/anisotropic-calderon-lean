import Calderon.PolynomialSlotCompatibility
import Calderon.FischerDensityIntegration

noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff
namespace OAI.AnisotropicCalderon.FiniteCovectorTransport
open RadiusProfile ConformalDepth AngularPolynomial MovingFrameConnection
  FischerConnectionTransport PolynomialSlotCompatibility FischerDensityIntegration

lemma fischer_covector_slot_cancellation (w : Fin 3 → Fin 3 → ℝ)
    (hw : ∀ a i,w a i = -w i a) (U V Q Z : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3,
      (fischerInner (Q i-∑ a : Fin 3, C (w a i) * U a) (V i) +
      fischerInner (U i) (Z i-∑ a : Fin 3, C (w a i) * V a))) =
      ∑ i : Fin 3, (fischerInner (Q i) (V i)+fischerInner (U i) (Z i)) := by
  have hnegL (p q : MvPolynomial (Fin 3) ℝ) : fischerInner (-p) q = -fischerInner p q := by
    simpa using fischerInner_C_mul_left (-1) p q
  have hnegR (p q : MvPolynomial (Fin 3) ℝ) : fischerInner p (-q) = -fischerInner p q := by
    simpa using fischerInner_C_mul_right (-1) p q
  have hsL (p q r : MvPolynomial (Fin 3) ℝ) : fischerInner (p-q) r = fischerInner p r-fischerInner q r := by
    simp only [sub_eq_add_neg,fischerInner_add_left,hnegL]
  have hsR (p q r : MvPolynomial (Fin 3) ℝ) : fischerInner p (q-r) = fischerInner p q-fischerInner p r := by
    simp only [sub_eq_add_neg,fischerInner_add_right,hnegR]
  have hd (a : Fin 3) : w a a=0 := by have h:=hw a a;linarith
  simp only [hsL,hsR,fischerInner_finset_sum_left,fischerInner_sum_right,
    fischerInner_C_mul_left,fischerInner_C_mul_right,Fin.sum_univ_three,
    fischerInner_add_left,fischerInner_add_right]
  rw [hd 0,hd 1,hd 2,hw 1 0,hw 2 0,hw 2 1]
  ring

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def finiteCovectorFischerPair (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x : R3) : ℝ :=
  ∑ i : Fin 3, fischerInner (finitePolynomialField (fun j=>b j i) c x)
    (finitePolynomialField (fun j=>d j i) z x)

lemma contDiff_finiteCovectorFischerPair (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) : ContDiff ℝ ∞ (finiteCovectorFischerPair b d c z) := by
  change ContDiff ℝ ∞ (fun x => ∑ i : Fin 3, fischerInner
    (finitePolynomialField (fun j => b j i) c x) (finitePolynomialField (fun j => d j i) z x))
  simp only [Fin.sum_univ_three]
  exact ((contDiff_fischerPair _ _ c z hc hz).add (contDiff_fischerPair _ _ c z hc hz)).add
    (contDiff_fischerPair _ _ c z hc hz)

lemma hasCompactSupport_finiteCovectorFischerPair (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : HasCompactSupport c) : HasCompactSupport (finiteCovectorFischerPair b d c z) := by
  change HasCompactSupport (fun x => ∑ i : Fin 3, fischerInner
    (finitePolynomialField (fun j => b j i) c x) (finitePolynomialField (fun j => d j i) z x))
  simp only [Fin.sum_univ_three]
  exact ((hasCompactSupport_fischerPair _ _ c z hc).add (hasCompactSupport_fischerPair _ _ c z hc)).add
    (hasCompactSupport_fischerPair _ _ c z hc)

theorem fderiv_finiteCovectorFischerPair (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (x V : R3) :
    fderiv ℝ (finiteCovectorFischerPair b d c z) x V =
      ∑ i : Fin 3,
        (fischerInner (referenceCovectorPolynomialDerivative g L lam b c x V i)
          (finitePolynomialField (fun j=>d j i) z x) +
        fischerInner (finitePolynomialField (fun j=>b j i) c x)
          (referenceCovectorPolynomialDerivative g L lam d z x V i)) := by
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin 3)), DifferentiableAt ℝ
      (fun y=>fischerInner (finitePolynomialField (fun j=>b j i) c y)
        (finitePolynomialField (fun j=>d j i) z y)) x :=
    fun i _=>(contDiff_fischerPair _ _ c z hc hz).differentiable (by simp) x
  change fderiv ℝ (fun y => ∑ i : Fin 3, fischerInner
    (finitePolynomialField (fun j => b j i) c y) (finitePolynomialField (fun j => d j i) z y)) x V = _
  rw [fderiv_fun_sum hi,ContinuousLinearMap.sum_apply]
  simp_rw [referenceCovariantPolynomialDerivative_fischer_compatible g hg L lam _ _ c z hc hz]
  exact (fischer_covector_slot_cancellation (referenceFrameConnectionCoefficient g L lam x V)
    (fun a i=>referenceFrameConnectionCoefficient_skew g hg L lam x V a i)
    (fun i=>finitePolynomialField (fun j=>b j i) c x)
    (fun i=>finitePolynomialField (fun j=>d j i) z x)
    (fun i=>referenceCovariantPolynomialDerivative g L lam (fun j=>b j i) c x V)
    (fun i=>referenceCovariantPolynomialDerivative g L lam (fun j=>d j i) z x V)).symm

theorem compact_reference_covector_fischer_contraction (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (rho : R3 → ℝ) (hr : ContDiff ℝ ∞ rho) (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3,rho x * (∑ i : Fin 3,
      (fischerInner (referenceCovectorPolynomialDerivative g L lam b c x (V x) i)
        (finitePolynomialField (fun j=>d j i) z x) +
      fischerInner (finitePolynomialField (fun j=>b j i) c x)
        (referenceCovectorPolynomialDerivative g L lam d z x (V x) i)))) =
      -(∫ x : R3,weightedCoordinateDivergence rho V x * finiteCovectorFischerPair b d c z x) := by
  have h:=compact_weighted_scalar_variable_adjoint rho (finiteCovectorFischerPair b d c z) V hr
    (contDiff_finiteCovectorFischerPair b d c z hc hz) hV
    (hasCompactSupport_finiteCovectorFischerPair b d c z hcompact)
  simpa only [fderiv_finiteCovectorFischerPair g hg L lam b d c z hc hz] using h

end OAI.AnisotropicCalderon.FiniteCovectorTransport
