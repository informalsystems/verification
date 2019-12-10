---------------------- MODULE LightclientV1P1H3N3 ------------------------
EXTENDS LightclientV1P1

OVERRIDE_TRUSTED_HEIGHT == 1
OVERRIDE_TO_VERIFY_HEIGHT == 3

OVERRIDE_AllNodes == { "p1", "p2", "p3", "p4" }
OVERRIDE_ULTIMATE_HEIGHT == 3

=============================================================================

