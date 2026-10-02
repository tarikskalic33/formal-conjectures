# Native build and negative proof probe

The ordinary library file is byte-identical to upstream main at
`02da1ad1288b4881ea1f8e575fbe84af7db04364` (blob
`c8d38bef385eb15661c3daf7449625b66b019b2a`). Its existing conjecture
placeholder is not an AEGIS proof and supplies no proof evidence.

Each Li workflow MUST reconstruct the original native negative probe before
its existing verification steps. The reconstructed file is byte-identical to
PR37's native target (blob `910ff74bbd5ef701b094a8b8edc04e697363f2d6`).
The paired workflows then perform their existing weighted-target substitution.
The actual native file is compiled, not a replacement theorem or a proxy.

No producer compilation, endpoint probe, axiom rejection or expected-error
check has been removed. Ordinary build success and the mandatory negative
probe are distinct results. A changed upstream baseline or prepared probe
fails closed. Run the six Python regression checks before preparation:

`python3 -m unittest discover -s AegisRH/Li -p test_prepare_native_probe.py`

These Python tests verify byte binding and mutation safety, not Lean proofs.
RH_PROVEN=FALSE; AUTHORITY_EFFECT=NONE. No merge or deployment is authorized.
