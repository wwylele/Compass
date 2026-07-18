# Straightedge and compass construction in Lean

[![Documentation](https://img.shields.io/badge/Documentation-passing-green)](https://wwylele.github.io/Compass/docs/)

This project formalizes some basic theory of [straightedge and compass construction](https://en.wikipedia.org/wiki/Straightedge_and_compass_construction) in Lean,
including a prove of theorem #8 from Freek Wiedijk's list of 100 theorems.

## Main declarations

- `EuclideanGeometry.ConstructiblePoint`: predicate for constructible points using straightedge and compass.
- `constructibleClosure`: constructible closure of a field. That is, the union of all iterated quadratic extensions of th field.
- `EuclideanGeometry.ConstructiblePoint.mem_constructibleClosure`: constructible points on the complex plane are in the constructible closure.
- `EuclideanGeometry.constructiblePoint_of_mem_constructibleClosure`: constructible numbers are all constructible points
- `EuclideanGeometry.not_exist_angle_trisection`: the impossibility of trisecting the angle.
- `EuclideanGeometry.not_exist_doubling_cube`: the impossibility of doubling the cube.