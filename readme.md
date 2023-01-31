googology（大数学）是研究如何构造尽可能大的自然数的学科。

本项目基于Coq给出googology中一些常用的定义，包括非形式化描述和形式化定义。

`Ordinal.v` 包含序数、序数运算、增长层级等基础定义

`Simple.v` 定义了一些简单的大数记号

`OrdIterFixpoint.v` 定义了序数函数迭代的不动点相关的一些构造，例如Veblen函数

`MadoreOCF.v` 、`BuchholzOCF.v` 定义与OCF对应的一些递归序数记号

`GH.v` 证明FGH和HH的换算，以及其它一些简单性质

`OrdArith.v` 证明序数运算的一些性质

`Eps0NormalForm.v` 给出了 $\epsilon_0$ 以内的序数的一种表示方式