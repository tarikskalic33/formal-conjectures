# AEGIS Ω — H64 scalarization V5 (16 October 2026)

**Evidence status:** explicit fixed-action linearization, exact variational
instability witness, independent executable SymPy/integer/scipy tests
25/25 PASS. This does **not** establish nonlinear gravity, a physical
emergence of spacetime, universal RH, or a Theory of Everything.

## Existing kernel-checked mathematical input

On the appropriate certified moment-zero common-window Weil packet
family (64 packets), the genuine complete Hermitian matrix
`G_ab=B(g_a,g_b)` gives a semidefinite form `K=-G⪰0`.
Every 64x64 entry is retained in
`Z=z†Kz=Σ_(a,b) conj(z_a) K_ab z_b`.
The H64 Walsh coordinate transform U=H64/8 is unitary and preserves
Z upon K→UKU† and z→Uz. These statements do not define a physical
field dynamics or select a physical length scale.

## One action fixed before field equations

In G=c=1 units and metric signature (-+++), specify

```text
S=∫ sqrt(-g) d4x [
  (1+xi*z†K*z)*R/(16*pi)
  - g^(mu,nu)*(∂mu z†)*K*(∂nu z)
  - m²*z†K*z - lambda4*(z†K*z)²
  + L_NED(F)
]
```

where K is a **fixed** nonzero Hermitian PSD matrix on a stated genuine
Weil family. NED is the **fixed-coupling** magnetic model from V2:
`L_NED=-(3*mu)/(4*pi) [s/(1+s)]^(5/2)`,
`s=sigma*sqrt(F)/sqrt(2)`. Here mu,sigma>0, m²>=0,
lambda4>=0, xi independent/free. The solution z=0 has A=1,
V=0, magnetic monopole F=2q²/r4, a²=sigma*q, M=mu*a³,
and the known Bardeen geometry

```text
f_B=1-2M*r²/(r²+a²)^(3/2), Phi_B=0,
R_B=6M*a²*(4a²-r²)/(r²+a²)^(7/2), R_B(0)=24mu.
```

This is a standard GR+NED background, NOT gravity derived from H64.

## Exact first-order scalar perturbation

Choose any v with v†Kv=1, let z=epsilon*phi*v.
The metric, NED and A=1+xi*Z receive no O(epsilon)
perturbation. Variation of the prescribed action therefore gives

```text
[Box_B - m² + xi*R_B/(16*pi)] phi=0.
```

For phi(t,r)=exp(s*t)u(r), spherical l=0,

```text
(r²*f_B*u')' +r² [xi*R_B/(16*pi)-m²]u
    =s²*r²*u/f_B.
Q_xi[u]=∫r² [f_B*(u')²+(m²-xi*R_B/(16*pi))*u²] dr.
```

When f_B>0, negative Q on a regular finite-norm trial function
implies negative spatial spectrum and a linearly growing mode
under the usual self-adjoint regular-center/asymptotic domain.
The proof is *linearized*, not a nonlinear existence theorem.

For xi>=0, R_B<=24mu. The sufficient positivity/no-static-hair
region is `xi <= 2*pi*m²/(3*mu)` for regular decaying static
modes where the integrated boundary term vanishes.

## Exact analytic instability on one horizonless example

Choose a=1, M=1/2, m=0. Then
`f_B=1-r²/(1+r²)^(3/2) > 0` everywhere,
`R_B=3*(4-r²)/(1+r²)^(7/2)`.
Select the compact C1 trial
`u(r)=(1-r²)²` for 0<=r<=1, 0 otherwise.

On its support `f_B<=1` and `R_B>=3/4` (the latter
by monotonicity and R_B(1)=9/(8sqrt(2))>3/4).
All integrals are EXACT rational:
```text
∫_0^1 r²*u'² dr =128/315
∫_0^1 r²*u²  dr =128/3465
Lambda = xi/(16*pi).
Lambda=15, i.e. xi=240*pi:
Q_xi[u] <=128/315-15*(3/4)*(128/3465)
        =-32/3465 <0.
```
This is a strict sufficient criterion for linear instability of
the explicitly fixed Einstein-NED-scalar action at this parameter
point. It is NOT a claimed measured or uniquely H64-determined coupling.

## Separate finite-radius numerical onset probe

A massless l=0 regular static mode solves
`(r²f_Bu')'+Lambda*r²*R_B*u=0`.
Use u(0)=1,u'(0)=0 and eliminate the constant asymptotic term
approximately via u(L)+L*u'(L)=0. Independent scipy solve_ivp +
brentq gives (L/a,Lambda):
(100,0.478371554);(200,0.478380508);
(400,0.478382729);(800,0.478383283).
Thus the estimated onset `Lambda_crit≈0.4783835`,
`xi_crit≈24.0462`, is NUMERICAL, not a rigorous enclosure
or a proof of a nonlinear branch.

## Nontrivial checks against V4 false closure

The V4 minimal profile z=a² v/(r²+a²) and its computed
lapse Phi do not solve the free massless scalar field equation
when the old Bardeen NED is kept. The equation residual is

```text
(r²*f_B*z')'+r²*f_B*Phi'*z'
      = 2a²/r² + O(r^-3).
```

The angular Einstein equation with the unchanged Bardeen
source has an independent residual
`-128*pi*a^4/r^6 + O(r^-7)` for normalized amplitude.
A radial Einstein projection alone must NOT be accepted as a
complete field solution.

## Evidence and exact remaining conditions

Conversation artifacts: `H64_SCALARIZATION_V5.md`,
`verify_h64_scalarization_v5.py`,
`H64_SCALARIZATION_V5_verified.json` were independently
written and executed locally; 25/25 checks PASS.
The 64-way integer-witness K used to test matrix conjugation
is **synthetic**, not an actual arithmetic Weil sample.
This commit adds the research receipt; it does NOT add a
Lean-kernel physics proof or execute a new RH terminal.

Next falsifiable step: fix or derive the gravitational couplings
xi, m, lambda4 from physical packet dynamics; obtain a self-consistent
back-reacted solution of ALL coupled Einstein, scalar and NED
equations with conserved stress and measurable asymptotics.
Do not use scalarization of a pre-existing Bardeen background
as proof of complete emergent physical spacetime.

Prior physics: Ayón-Beato & García, *Phys. Lett. B* 493
(2000) 149–152, DOI 10.1016/S0370-2693(00)01125-4.
