<?php
require_once '..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{n - 1} {x} \\cos^{m - 1} {x}\\, dx = \\frac{\\operatorname{B}\\left(\\frac{m}{2}, \\frac{n}{2}\\right)}{2}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{n - 1} {x} \\cos^{m - 1} {x}\\, dx = \\frac{\\Gamma\\left(\\frac{m}{2}\\right) \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{m}{2} + \\frac{n}{2}\\right)}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{n - 1} {x}\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{n - 1} {x}\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\frac{\\sin^{n} {x} \\cos {x} \\cos^{m} {x}}{\\sin {x}}\\, dx = \\frac{\\Gamma\\left(\\frac{n}{2}\\right) \\Gamma\\left(\\frac{m}{2} + 1\\right)}{2 \\Gamma\\left(\\frac{m}{2} + \\frac{n}{2} + 1\\right)}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\frac{m \\int\\limits_{0}^{\\frac{\\pi}{2}} \\frac{\\sin {x} \\sin^{n} {x} \\cos^{m} {x}}{\\cos {x}}\\, dx}{n} = \\frac{\\Gamma\\left(\\frac{n}{2}\\right) \\Gamma\\left(\\frac{m}{2} + 1\\right)}{2 \\Gamma\\left(\\frac{m}{2} + \\frac{n}{2} + 1\\right)}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\frac{\\sin {x} \\sin^{n} {x} \\cos^{m} {x}}{\\cos {x}}\\, dx = \\frac{n \\Gamma\\left(\\frac{n}{2}\\right) \\Gamma\\left(\\frac{m}{2} + 1\\right)}{2 m \\Gamma\\left(\\frac{m}{2} + \\frac{n}{2} + 1\\right)}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\frac{\\sin {x} \\sin^{n} {x} \\cos^{m} {x}}{\\cos {x}}\\, dx = \\frac{n \\Gamma\\left(\\frac{m}{2}\\right) \\Gamma\\left(\\frac{n}{2}\\right)}{2 m \\Gamma\\left(\\frac{m}{2} + \\frac{n}{2}\\right) + 2 n \\Gamma\\left(\\frac{m}{2} + \\frac{n}{2}\\right)}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\frac{\\sin {x} \\sin^{n} {x} \\cos^{m} {x}}{\\cos {x}}\\, dx = \\frac{n \\Gamma\\left(\\frac{m}{2}\\right) \\Gamma\\left(\\frac{n}{2}\\right)}{2 m \\Gamma\\left(\\frac{m}{2} + \\frac{n}{2}\\right) + 2 n \\Gamma\\left(\\frac{m}{2} + \\frac{n}{2}\\right)}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{n - 1} {x} \\cos {x}\\, dx = \\frac{\\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + 1\\right)}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\frac{1}{n} = \\frac{\\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + 1\\right)}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

