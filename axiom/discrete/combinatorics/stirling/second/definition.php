<?php
require_once '..\..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k}\\end{matrix}\\right\\} = \\frac{\\sum\\limits_{l=0}^{k} \\left(-1\\right)^{k + l} l^{n} {\\binom{k}{l}}}{k!}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n + 1}\\\\{k + 1}\\end{matrix}\\right\\} = \\left(k + 1\\right) \\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} + \\left\\{\\begin{matrix}{n}\\\\{k}\\end{matrix}\\right\\}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n + 1}\\\\{k + 1}\\end{matrix}\\right\\} = \\left(k + 1\\right) \\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} + \\frac{\\sum\\limits_{l=0}^{k} \\left(-1\\right)^{k + l} l^{n} {\\binom{k}{l}}}{k!}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\({y}_{n} = \\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\({y}_{n + 1} = \\left\\{\\begin{matrix}{n + 1}\\\\{k + 1}\\end{matrix}\\right\\}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\({y}_{n + 1} = {y}_{n} \\left(k + 1\\right) + \\frac{\\sum\\limits_{l=0}^{k} \\left(-1\\right)^{k + l} l^{n} {\\binom{k}{l}}}{k!}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{{y}_{n} = - \\frac{\\left(-1\\right)^{k} \\sum\\limits_{l=0}^{k} \\frac{\\left(-1\\right)^{l} l^{n} {\\binom{k}{l}}}{k - l + 1}}{k!} + C_{0} \\left(k + 1\\right)^{n}}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} = - \\frac{\\left(-1\\right)^{k} \\sum\\limits_{l=0}^{k} \\frac{\\left(-1\\right)^{l} l^{n} {\\binom{k}{l}}}{k - l + 1}}{k!} + C_{0} \\left(k + 1\\right)^{n}}\\tag*{Eq.stirling_solution}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{1 = - \\frac{\\left(-1\\right)^{k} \\sum\\limits_{l=1}^{k} \\frac{\\left(-1\\right)^{l} l^{k + 1} {\\binom{k}{l}}}{k - l + 1}}{k!} + C_{0} \\left(k + 1\\right)^{k + 1}}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{\\left(\\left(- \\frac{1}{k + 1}\\right)^{k} \\sum\\limits_{l=1}^{k} \\frac{\\left(-1\\right)^{l} l l^{k}}{\\left(k - l + 1\\right) l! \\left(k - l\\right)!} + \\left(k + 1\\right)^{- k}\\right) k!}{\\left(k + 1\\right)!}}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{\\left(\\left(- \\frac{1}{k + 1}\\right)^{k} \\sum\\limits_{l=1}^{k} \\frac{\\left(-1\\right)^{l} l^{k + 1}}{\\left(k - l + 1\\right) l! \\left(k - l\\right)!} + \\left(k + 1\\right)^{- k}\\right) k!}{\\left(k + 1\\right)!}}\\tag*{Eq.exist_C0}\\)";
$txt[$i++] = "\\({\\binom{k + 1}{l}} = \\frac{\\left(k + 1\\right)!}{l! \\left(k - l + 1\\right)!}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\left(k - l + 1\\right)! = \\left(k - l + 1\\right) \\left(k - l\\right)!\\tag*{Eq.factorial_expand_kl}\\)";
$txt[$i++] = "\\({\\binom{k + 1}{l}} = \\frac{\\left(k + 1\\right)!}{\\left(k - l + 1\\right) l! \\left(k - l\\right)!}\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\frac{{\\binom{k + 1}{l}}}{\\left(k + 1\\right)!} = \\frac{1}{k l! \\left(k - l\\right)! - l l! \\left(k - l\\right)! + l! \\left(k - l\\right)!}\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\(\\frac{1}{k l! \\left(k - l\\right)! - l l! \\left(k - l\\right)! + l! \\left(k - l\\right)!} = \\frac{{\\binom{k + 1}{l}}}{\\left(k + 1\\right)!}\\tag*{Eq[12]}\\)";
$txt[$i++] = "\\(\\left(k + 1\\right)! = \\left(k + 1\\right) k!\\tag*{Eq.factorial_expand}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{\\left(- \\frac{1}{k + 1}\\right)^{k} \\sum\\limits_{l=1}^{k} \\frac{\\left(-1\\right)^{l} l^{k + 1}}{\\left(k - l + 1\\right) l! \\left(k - l\\right)!} + \\left(k + 1\\right)^{- k}}{k + 1}}\\tag*{Eq[13]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{\\left(- \\frac{1}{k + 1}\\right)^{k} \\sum\\limits_{l=1}^{k} \\frac{\\left(-1\\right)^{l} l^{k + 1}}{\\left(k - l + 1\\right) l! \\left(k - l\\right)!}}{k + 1} + \\frac{\\left(k + 1\\right)^{- k}}{k + 1}}\\tag*{Eq[14]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{\\left(- \\frac{1}{k + 1}\\right)^{k} \\sum\\limits_{l=1}^{k} \\frac{\\left(-1\\right)^{l} l^{k + 1}}{\\left(k - l + 1\\right) l! \\left(k - l\\right)!}}{k + 1} + \\left(k + 1\\right)^{- k - 1}}\\tag*{Eq.exist_C0}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{\\left(- \\frac{1}{k + 1}\\right)^{k} \\sum\\limits_{l=1}^{k} \\frac{\\left(-1\\right)^{l} l^{k + 1}}{l! \\left(k - l + 1\\right)!}}{k + 1} + \\left(k + 1\\right)^{- k - 1}}\\tag*{Eq.exist_C0}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{k + 1}\\ {x^{k + 1}} = \\sum\\limits_{l=0}^{k + 1} \\left(-1\\right)^{k + l + 1} \\left(l + x\\right)^{k + 1} {\\binom{k + 1}{l}}\\tag*{Eq[15]}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{k + 1}\\ {x^{k + 1}} = \\left(k + 1\\right)!\\tag*{Eq[16]}\\)";
$txt[$i++] = "\\(\\left(k + 1\\right)! = \\sum\\limits_{l=0}^{k + 1} \\left(-1\\right)^{k + l + 1} \\left(l + x\\right)^{k + 1} {\\binom{k + 1}{l}}\\tag*{Eq[17]}\\)";
$txt[$i++] = "\\(\\left(k + 1\\right)! = \\sum\\limits_{l=1}^{k + 1} \\left(-1\\right)^{k + l + 1} l^{k + 1} {\\binom{k + 1}{l}}\\tag*{Eq[18]}\\)";
$txt[$i++] = "\\(\\left(-1\\right)^{k + 1} \\left(k + 1\\right)! = \\left(-1\\right)^{k + 1} \\sum\\limits_{l=1}^{k + 1} \\left(-1\\right)^{k + l + 1} l^{k + 1} {\\binom{k + 1}{l}}\\tag*{Eq[19]}\\)";
$txt[$i++] = "\\(\\left(-1\\right)^{k + 1} \\left(k + 1\\right)! = \\sum\\limits_{l=1}^{k + 1} \\left(-1\\right)^{k + 1} \\left(-1\\right)^{k + l + 1} l^{k + 1} {\\binom{k + 1}{l}}\\tag*{Eq[20]}\\)";
$txt[$i++] = "\\(\\left(-1\\right)^{k + 1} \\left(k + 1\\right)! = \\sum\\limits_{l=1}^{k + 1} \\left(-1\\right)^{l} l^{k + 1} {\\binom{k + 1}{l}}\\tag*{Eq[21]}\\)";
$txt[$i++] = "\\(\\left(-1\\right)^{k + 1} \\left(k + 1\\right)! = \\left(-1\\right)^{k + 1} \\left(k + 1\\right)^{k + 1} + \\sum\\limits_{l=1}^{k} \\left(-1\\right)^{l} l^{k + 1} {\\binom{k + 1}{l}}\\tag*{Eq[22]}\\)";
$txt[$i++] = "\\(- \\left(-1\\right)^{k + 1} \\left(k + 1\\right)^{k + 1} + \\left(-1\\right)^{k + 1} \\left(k + 1\\right)! = \\sum\\limits_{l=1}^{k} \\left(-1\\right)^{l} l^{k + 1} {\\binom{k + 1}{l}}\\tag*{Eq[23]}\\)";
$txt[$i++] = "\\(- \\left(-1\\right)^{k} + \\frac{\\left(-1\\right)^{k} k \\left(k + 1\\right)^{k} + \\left(-1\\right)^{k} \\left(k + 1\\right)^{k}}{\\left(k + 1\\right)!} = \\sum\\limits_{l=1}^{k} \\frac{\\left(-1\\right)^{l} l l^{k}}{l! \\left(k - l + 1\\right)!}\\tag*{Eq[24]}\\)";
$txt[$i++] = "\\(- \\left(-1\\right)^{k} + \\frac{\\left(-1\\right)^{k} k \\left(k + 1\\right)^{k} + \\left(-1\\right)^{k} \\left(k + 1\\right)^{k}}{\\left(k + 1\\right)!} = \\sum\\limits_{l=1}^{k} \\frac{\\left(-1\\right)^{l} l^{k + 1}}{l! \\left(k - l + 1\\right)!}\\tag*{Eq[25]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{\\left(- \\frac{1}{k + 1}\\right)^{k} \\left(- \\left(-1\\right)^{k} + \\frac{\\left(-1\\right)^{k} k \\left(k + 1\\right)^{k} + \\left(-1\\right)^{k} \\left(k + 1\\right)^{k}}{\\left(k + 1\\right) k!}\\right)}{k + 1} + \\left(k + 1\\right)^{- k - 1}}\\tag*{Eq[26]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{k}{k^{2} k! + 2 k k! + k!} + \\frac{1}{k^{2} k! + 2 k k! + k!}}\\tag*{Eq[27]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{1}{k k! + k!}}\\tag*{Eq[28]}\\)";
$txt[$i++] = "\\(\\exists_{C_{0}}{C_{0} = \\frac{1}{\\left(k + 1\\right)!}}\\tag*{Eq[29]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} = - \\frac{\\left(-1\\right)^{k} \\sum\\limits_{l=0}^{k} \\frac{\\left(-1\\right)^{l} l^{n} {\\binom{k}{l}}}{k - l + 1}}{k!} + \\frac{\\left(k + 1\\right)^{n}}{\\left(k + 1\\right)!}\\tag*{Eq.stirling_solution}\\)";
$txt[$i++] = "\\({\\binom{k + 1}{k - l + 1}} = \\frac{\\left(k + 1\\right) {\\binom{k}{k - l}}}{k - l + 1}\\tag*{Eq[30]}\\)";
$txt[$i++] = "\\({\\binom{k}{l}} = {\\binom{k}{k - l}}\\tag*{Eq[31]}\\)";
$txt[$i++] = "\\({\\binom{k + 1}{l}} = {\\binom{k + 1}{k - l + 1}}\\tag*{Eq[32]}\\)";
$txt[$i++] = "\\({\\binom{k + 1}{l}} = \\frac{\\left(k + 1\\right) {\\binom{k}{l}}}{k - l + 1}\\tag*{Eq[33]}\\)";
$txt[$i++] = "\\(\\frac{{\\binom{k + 1}{l}}}{k + 1} = \\frac{{\\binom{k}{l}}}{k - l + 1}\\tag*{Eq[34]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} = - \\frac{\\left(-1\\right)^{k} \\sum\\limits_{l=0}^{k} \\left(-1\\right)^{l} l^{n} {\\binom{k + 1}{l}}}{\\left(k + 1\\right) k!} + \\frac{\\left(k + 1\\right)^{n}}{\\left(k + 1\\right)!}\\tag*{Eq[35]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} = - \\frac{\\left(-1\\right)^{k} \\sum\\limits_{l=0}^{k} \\left(-1\\right)^{l} l^{n} {\\binom{k + 1}{l}}}{\\left(k + 1\\right)!} + \\frac{\\left(k + 1\\right)^{n}}{\\left(k + 1\\right)!}\\tag*{Eq[36]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} \\left(k + 1\\right)! = \\left(- \\frac{\\left(-1\\right)^{k} \\sum\\limits_{l=0}^{k} \\left(-1\\right)^{l} l^{n} {\\binom{k + 1}{l}}}{\\left(k + 1\\right)!} + \\frac{\\left(k + 1\\right)^{n}}{\\left(k + 1\\right)!}\\right) \\left(k + 1\\right)!\\tag*{Eq[37]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} \\left(k + 1\\right)! = - \\left(-1\\right)^{k} \\sum\\limits_{l=0}^{k} \\left(-1\\right)^{l} l^{n} {\\binom{k + 1}{l}} + \\left(k + 1\\right)^{n}\\tag*{Eq[38]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} \\left(k + 1\\right)! = \\left(k + 1\\right)^{n} + \\sum\\limits_{l=0}^{k} - \\left(-1\\right)^{k} \\left(-1\\right)^{l} l^{n} {\\binom{k + 1}{l}}\\tag*{Eq[39]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} \\left(k + 1\\right)! = \\left(k + 1\\right)^{n} + \\sum\\limits_{l=0}^{k} \\left(-1\\right)^{k + l + 1} l^{n} {\\binom{k + 1}{l}}\\tag*{Eq[40]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} \\left(k + 1\\right)! = \\sum\\limits_{l=0}^{k + 1} \\left(-1\\right)^{k + l + 1} l^{n} {\\binom{k + 1}{l}}\\tag*{Eq[41]}\\)";
$txt[$i++] = "\\(\\left\\{\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right\\} \\left(k + 1\\right)! = \\left(k + 1\\right)^{n} + \\sum\\limits_{l=0}^{k} \\left(-1\\right)^{k + l + 1} l^{n} {\\binom{k + 1}{l}}\\tag*{Eq[40]}\\)";
render(__FILE__, $txt);
?>        

