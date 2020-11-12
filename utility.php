<?php
include_once 'index.html';

// use the following regex to remove error_log prints:^ +error_log

// to speed up the .php page rendering, disable error_log!!
$sagemath = basename(dirname(__file__));

function get_extension($file)
{
    return pathinfo($file, PATHINFO_EXTENSION);
}

function startsWith($haystack, $needle)
{
    $length = strlen($needle);
    return substr($haystack, 0, $length) === $needle;
}

function endsWith($haystack, $needle)
{
    $length = strlen($needle);
    if ($length == 0) {
        return true;
    }

    return substr($haystack, - $length) === $needle;
}

function quote($param)
{
    if (strpos($param, "'") !== false) {
        $param = str_replace("'", "&apos;", $param);
    }

    return $param;
}

function str_html($param)
{
    // preg_replace()
    return preg_replace("/<(?=[a-zA-Z!\/])/", "&lt;", str_replace("&", "&amp;", $param));
}

function create_html_tag(&$statement, &$axiom_prefix)
{
    // Eq << Eq.x_j_subset.apply(discrete.sets.subset.nonemptyset, Eq.x_j_inequality, evaluate=False)
    if (preg_match('/\.apply\((.+)\)/', $statement, $matches)) {
        $theorem = preg_split("/\s*,\s*/", $matches[1], - 1, PREG_SPLIT_NO_EMPTY)[0];
        // error_log('create_a_tag: ' . __LINE__);
        return create_a_tag($theorem, $statement, $axiom_prefix);
    } else {
        return create_text_tag($statement);
    }
}

function create_text_tag(&$statement)
{
    $length = strlen($statement);
    $statement_quote = quote($statement);
    return "<input name=python[] size = $length value = '$statement_quote'>";
}

function create_a_tag_with_request(&$statement, $module)
{
    $length = strlen($statement);
    $statement_quote = quote($statement);
    global $sagemath;
    $request_url = "/$sagemath/request.php?callee=$module";
    return "<a name=python[] href='$request_url'>$statement_quote</a>";
}

function create_a_tag($theorem, &$statement, &$axiom_prefix)
{
    // error_log("theorem = $theorem");
    // error_log("statement = $statement");
    // error_log("axiom_prefix = " . jsonify($axiom_prefix));
    // error_log("__file__ = " . __file__);
    // error_log("dirname(__file__) = " . dirname(__file__));
    $dot_index = strpos($theorem, '.');
    if ($dot_index === false) {
        $head = $theorem;
    } else {
        $head = substr($theorem, 0, $dot_index);
    }

    $theorem = str_replace(".", "/", $theorem);

    $prefix = $axiom_prefix[$head];

    global $sagemath;
    if ($prefix)
        $full_theorem_path = "/$sagemath/$prefix";
    else
        $full_theorem_path = "/$sagemath";

    $full_theorem_path .= "/$theorem.php";

    // error_log('full_theorem_path = ' . $full_theorem_path);

    $statement_quote = str_html($statement);
    return "<a name=python[] href='$full_theorem_path'>$statement_quote</a>";
}

function analyze_apply($py, &$i)
{
    // ++ $i;
    $numOfYields = 0;
    for (; $i < count($py); ++ $i) {
        $statement = $py[$i];
        if (preg_match('/^def +prove\(Eq(, *\w+)?\) *: */', $statement, $matches)) {
            // error_log('prove begins: ' . $statement);
            break;
        }

        if (preg_match('/^@check/', $statement, $matches)) {
            continue;
        }

        if (preg_match('/^from/', $statement, $matches)) {
            continue;
        }

        if (preg_match('/^ *$/', $statement, $matches)) {
            continue;
        }

        if (preg_match('/^(?:    )+return +(.+) */', $statement, $matches)) {
            // error_log('return statement: ' . $statement);
            $yield = $matches[1];
            // error_log('return ' . $yield);
            if (! strcmp($yield, 'None'))
                continue;
            $balancedParanthesis = "(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\))";
            if (preg_match("/^(\w+)$balancedParanthesis *$/", $yield, $matches)) {
                // error_log($matches[1]);
                $numOfYields = 1;
            } else if (preg_match_all("/(\w+)$balancedParanthesis */", $yield, $matches, PREG_SET_ORDER)) {
                // https://www.php.net/manual/en/function.preg-match-all.php
                // error_log("matches = " . jsonify($matches));
                $numOfYields = count($matches);
            } else {
                $yield .= $py[$i + 1];
                if (preg_match_all("/(\w+)$balancedParanthesis */", $yield, $matches, PREG_SET_ORDER)) {
                    $numOfYields = count($matches);
                    ++ $i;
                }
            }
        }
    }

    return $numOfYields;
}

function to_python_module($py)
{
    global $sagemath;
    $module = [];
    $pythonFile = $py;
    for (;;) {
        $dirname = dirname($pythonFile);
        $basename = basename($pythonFile);
        if (! strcmp($basename, $sagemath)) {
            break;
        }

        $module[] = $basename;
        $pythonFile = $dirname;
    }

    $module[0] = substr($module[0], 0, - strlen(get_extension($module[0])) - 1);
    $module = array_reverse($module);

    $module = join('.', $module);
    return $module;
}

// input is a php file
function render($php)
{
    // error_log("php file = $php");
    $py = str_replace('.php', '.py', $php);
    // $py = str_replace('latex', 'sympy', $py);
    // error_log("python file = $py");

    assert(file_exists($py), "file_exists($py)");

    $inputs = [];
    $input = [];

    $axiom_prefix = [];
    $py = file($py);
    for ($i = 0; $i < count($py); ++ $i) {
        $statement = $py[$i];
        // error_log("$statement");
        // from axiom.neuron import bilinear # python import statement
        if (preg_match('/^from +(.+) +import +(.*)/', $statement, $matches)) {

            $prefix = $matches[1];
            $namespaces = $matches[2];
            $namespaces = preg_split("/[\s,]+/", $namespaces, - 1, PREG_SPLIT_NO_EMPTY);

            // error_log("end(namespaces) = " . end($namespaces));
            if (! strcmp(end($namespaces), '\\')) {
                // error_log("strcmp = " . strcmp(end($namespaces), '\\'));
                array_pop($namespaces);

                $statement = $py[++ $i];
                // error_log("$statement");

                $namespaces_addition = preg_split("/[\s,]+/", $statement, - 1, PREG_SPLIT_NO_EMPTY);
                // error_log("namespaces_addition = " . jsonify($namespaces_addition));

                $namespaces = array_merge($namespaces, $namespaces_addition);

                // error_log("namespaces = " . jsonify($namespaces));
            }

            $prefix_path = str_replace(".", "/", $prefix);

            foreach ($namespaces as $namespace) {
                // error_log('prefix detected: ' . $prefix . '.' . $namespace);
                $axiom_prefix[$namespace] = $prefix_path;
            }

            continue;
        }

        if (preg_match('/^import +(.+)/', $statement, $matches)) {
            // error_log('import statement: ' . $statement);
            $packages = $matches[1];
            $packages = preg_split("/\s*,\s*/", $packages, - 1, PREG_SPLIT_NO_EMPTY);

            foreach ($packages as $package) {
                $package = preg_split("/\s+/", $package, - 1, PREG_SPLIT_NO_EMPTY);
                // error_log('count(package) = ' . count($package));

                switch (count($package)) {
                    case 1:
                        $package = $package[0];
                        $axiom_prefix[$package] = '';
                        break;
                    case 2:
                        // error_log('count(package[0]) = ' . $package[0]);
                        // error_log('count(package[1]) = ' . $package[1]);
                        break;
                    case 3:
                        // error_log('count(package[0]) = ' . $package[0]);
                        // error_log('count(package[1]) = ' . $package[1]);
                        // error_log('count(package[2]) = ' . $package[2]);
                        $axiom_prefix[end($package)] = '';
                        // error_log('package detected: ' . $package[0]);
                        break;
                    default:
                        break;
                }
            }

            continue;
        }

        if (preg_match('/^def +apply\([^)]*\) *: */', $statement, $matches)) {
            // error_log('given begins: ' . $statement);
            $numOfYields = analyze_apply($py, $i);
            // error_log('given ended: ' . $statement);
            break;
        }
    }

    // error_log('axiom_prefix: ' . jsonify($axiom_prefix));

//     error_log("numOfYields = $numOfYields");

    $lengths = [];
    echo "<h3><font color=blue>given:</font></h3>";

    $indexOfYield = - 1;
    $counterOfLengths = 0;
    for (++ $i; $i < count($py); ++ $i) {
        $statement = $py[$i];
        // error_log("$statement");
        $statement = rtrim($statement);
        // remove comments starting with #
        if (preg_match('/^\s*#.*/', $statement, $matches) || ! $statement) {
            continue;
        }

        // the start of the next global statement other than def prove
        if (! startsWith($statement, '    ')) {
            break;
        }

        $statement = substr($statement, 4);

        if (preg_match('/([\w.]+)\.apply\(/', $statement, $matches)) {
            $theorem = $matches[1];
            // error_log('theorem detected: ' . $theorem);

            if (startsWith($theorem, '.')) {
                // consider the case
                // Eq << Eq[-1].reversed.apply(axiom.discrete.sets.inequality.notcontains, evaluate=False)
                $input[] = create_html_tag($statement, $axiom_prefix);
            } else if (strpos($theorem, 'Eq.') === false) {

                // error_log('create_a_tag: ' . __LINE__);
                // error_log("statement = $statement");
                $input[] = create_a_tag($theorem, $statement, $axiom_prefix);
            } else {
                $input[] = create_html_tag($statement, $axiom_prefix);
            }
        } else if (preg_match('/(=|<<) *apply\(/', $statement, $matches)) {
            // error_log('yield statement: ' . $statement);
            $indexOfYield = $counterOfLengths;
//             error_log("php = $php");
            $module = to_python_module($php);

//             error_log("module = $module");
            
            $input[] = create_a_tag_with_request($statement, $module);
        } else {
            $input[] = create_html_tag($statement, $axiom_prefix);
        }

        if (preg_match('/Eq *<< */', $statement, $matches)) {
            $inputs[] = join("<br>", $input);
            unset($input);

            ++ $counterOfLengths;
            $lengths[] = 1;
        } else if (preg_match('/(Eq\.\w+ *(?:, *(?:Eq\.\w+|\w+|\*\w+) *)*)= */', $statement, $matches)) {
            $statement = $matches[1];
            // error_log("parameter: " . $statement);

            preg_match_all('/Eq\.\w+/', $statement, $matches, PREG_SET_ORDER);

            ++ $counterOfLengths;
            $lengths[] = count($matches);

            $inputs[] = join("<br>", $input);
            unset($input);
        } else {
            // error_log("python statements: $statement");
        }
    }

//     error_log("indexOfYield = $indexOfYield");

    $numOfReturnsFromApply = $lengths[$indexOfYield];
    // error_log("numOfReturnsFromApply = " . $numOfReturnsFromApply);

    $p = [];
    $i = 0;
    $statements = '';
    $statements_before_yield = '';
    foreach (file($php) as &$statement) {
        // error_log($statement);
        if (strncmp($statement, "//", 2) !== 0) {
            continue;
        }

        $statement = substr($statement, 2);

        if ($i == $indexOfYield) {

            // error_log($statement);
            -- $lengths[$i];
            $statements .= $statement;
            if ($lengths[$i] == 0) {

                if ($numOfReturnsFromApply == 1) {
                    if (preg_match_all('/\\\\[(].+?\\\\[)]/', $statements, $matches, PREG_SET_ORDER)) {
                        // error_log("matches = ".jsonify($matches));
                        $numOfReturnsFromApply = count($matches);
                        // error_log("count(matches) = ".$numOfReturnsFromApply);

                        $statements_before_yield = array_slice($matches, 0, $numOfReturnsFromApply - $numOfYields);
                        // error_log("statements_before_yield = ".jsonify($statements_before_yield));
                        $statements = array_slice($matches, $numOfReturnsFromApply - $numOfYields);
                        // error_log("statements_after_yield = ".jsonify($statements));

                        foreach ($statements as &$statement) {
                            $statement = $statement[0];
                        }
                        $statements = join('', $statements);

                        foreach ($statements_before_yield as &$statement) {
                            $statement = $statement[0];
                        }
                        $statements_before_yield = join('', $statements_before_yield);
                    }
                }

                $p[] = "<p>$statements_before_yield</p><h3><font color=blue>yield:</font></h3><p>$statements</p><h3><font color=blue>prove:</font></h3>";

                $statements = '';
                $statements_before_yield = '';
                ++ $i;
            } else if ($lengths[$i] <= $numOfYields) {
                $statements_before_yield = "$statements";
                // error_log("statements_before_yield = $statements_before_yield");

                $statements = '';
            }
        } else {
            $statements .= $statement;
            -- $lengths[$i];
            if ($lengths[$i] == 0) {
                $p[] = "<p>$statements</p>";
                $statements = '';
                ++ $i;
            }
        }
    }

    $size = min(count($inputs), count($p));
    for ($i = 0; $i < $size; ++ $i) {
        echo $inputs[$i];
        $statement = $p[$i];
        // if ($json) {
        // https://www.php.net/manual/en/function.preg-match-all.php
        // if (preg_match_all('/\\\tag\*\{(Eq\[(\d+)\])\}/', $statement, $matches, PREG_SET_ORDER) || preg_match_all('/\\\tag\*\{(Eq\.(\w+))\}/', $statement, $matches, PREG_SET_ORDER)) {

        // foreach ($matches as &$match) {
        // $index = $match[2];
        // if (array_key_exists($index, $json)) {

        // $statement = str_replace("$match[1]", "$json[$index]=>$match[1]", $statement);
        // }
        // }
        // }
        // }
        echo $statement;
    }
}

function reference(&$value)
{
    if (is_array($value)) {
        foreach ($value as &$element) {
            $element = reference($element);
        }
        $value = join(', ', $value);
        return $value;
    }
    if (preg_match('/\d+/', $value, $matches)) {
        $value = (int) $value;
        if ($value < 0)
            return "plausible";
        return "Eq[$value]";
    } else {
        return "Eq.$value";
    }
}

function jsonify($param)
{
    return json_encode($param, JSON_UNESCAPED_UNICODE);
}

function println($param, $file = null)
{
    if (is_array($param)) {
        $param = jsonify($param);
    }

    if ($file) {
        echo "called in $file:<br>";
    }
    print_r($param);
    print_r("<br>");
}

?>
