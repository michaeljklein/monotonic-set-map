# monotonic-set-map

Experiments with writing `mapMonotonicallyIncreasing` for non-strictly monotonically increasing maps.

```haskell
mapMonotonicallyIncreasing :: Eq b => (a -> b) -> Set a -> Set b
```


## Benchmarks

The main executable contains the `criterion` benchmarks, build and run with:

```bash
stack build
stack exec -- monotonic-set-map-exe
```


## Tests

The tests may be run with:

```bash
stack test
```


# Docs

Haddock generated documentation may be found [here](https://michaeljklein.github.io/monotonic-set-map/)

