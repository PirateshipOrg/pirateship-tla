# PirateShip TLA+

A TLA+ specification of the
[PirateShip consensus protocol](https://github.com/PirateshipOrg/pirateship).
The model covers normal operation, view changes, Byzantine behavior, and crash
faults, with safety properties checked by TLC.

## Repository layout

- `pirateship.tla` contains the protocol specification.
- `TLCpirateship.tla` adds TLC initialization and monitoring helpers.
- `MCpirateship.tla` and `MCpirateship*.cfg` define exhaustive model checks.
- `SIMpirateship.tla` and `SIMpirateship*.cfg` define randomized simulations.
- `SIMpirateship.ipynb` analyzes simulation output.

## Running TLC

Install Java, then download the
[TLA+ tools](https://github.com/tlaplus/tlaplus/releases) and
[Community Modules](https://github.com/tlaplus/CommunityModules/releases) JARs
into the repository root as `tla2tools.jar` and `CommunityModules-deps.jar`.

Run an exhaustive crash-fault model check:

```sh
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto \
  -modelcheck MCpirateship.tla -config MCpirateshipCrash.cfg
```

Run a randomized Byzantine-fault simulation:

```sh
java -Dtlc2.tool.Simulator.extendedStatistics=true \
  -XX:+UseParallelGC -jar tla2tools.jar -workers auto \
  -simulate SIMpirateship.tla
```

The corresponding `MCpirateship.cfg` and `SIMpirateshipCrash.cfg`
configurations cover Byzantine model checking and crash-fault simulation.
