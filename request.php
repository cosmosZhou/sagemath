<?php
include_once 'index.html';

// 第1种方法：
// function get_extension($file)
// {
// substr(strrchr($file, '.'), 1);
// }

// // 第2种方法：
// function get_extension($file)
// {
// return substr($file, strrpos($file, '.') + 1);
// }

// // 第3种方法：
// function get_extension($file)
// {
// return end(explode('.', $file));
// }

// // 第4种方法：
// function get_extension($file)
// {
// $info = pathinfo($file);
// return $info['extension'];
// }

// 第5种方法：
function get_extension($file)
{
    return pathinfo($file, PATHINFO_EXTENSION);
}

function read_all_files($dir, $ext)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                $temp = $dir . DIRECTORY_SEPARATOR . $fl;

                if (is_dir($temp) && $fl != '.' && $fl != '..') {
                    // echo 'directory : ' . $temp . '<br>';
                    yield from read_all_files($temp, $ext);
                } else {
                    if ($fl != '.' && $fl != '..') {
                        if (! strcmp(get_extension($temp), $ext)) {
                            yield $temp;
                        }
                    }
                }
            }
        }
    }
}

function read_directory($dir)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                $temp = $dir . DIRECTORY_SEPARATOR . $fl;

                if (is_dir($temp) && $fl != '.' && $fl != '..') {
                    yield $temp;
                }
            }
        }
    }
}

function read_all_axioms($dir)
{
    foreach (read_directory($dir) as $directory) {
        foreach (read_all_files($directory, 'py') as $py) {
            if (strcmp(basename($py), "__init__.py")) {
                yield $py;
            }
        }
    }
}

function create_html_tag(&$statement, &$axiom_prefix, &$input)
{
    // Eq << Eq.x_j_subset.apply(discrete.sets.subset.nonemptyset, Eq.x_j_inequality, evaluate=False)
    if (preg_match('/\.apply\((.+)\)/', $statement, $matches)) {
        $theorem = preg_split("/\s*,\s*/", $matches[1], - 1, PREG_SPLIT_NO_EMPTY)[0];
        // error_log('create_a_tag: ' . __LINE__);
        $input[] = create_a_tag($theorem, $statement, $axiom_prefix);
    }
}

function str_html($param)
{
    // preg_replace()
    return preg_replace("/<(?=[a-zA-Z!\/])/", "&lt;", str_replace("&", "&amp;", $param));
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

    global $sagemath;

    $prefix = $axiom_prefix[$head];

    if ($prefix) {
        $prefix = str_replace('/', '.', $prefix);
        $module = "$prefix.$theorem";
    } else {
        $module = $theorem;
    }

    return $module;
    // return "<a name=python[] href='$full_theorem_path'>$module</a>";
}

function jsonify($param)
{
    return json_encode($param, JSON_UNESCAPED_UNICODE);
}

function startsWith($haystack, $needle)
{
    $length = strlen($needle);
    return substr($haystack, 0, $length) === $needle;
}

// input is a php file
function process_axiom($py)
{
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

        if (preg_match('/^def +prove\(Eq(, *\w+)?\) *: */', $statement, $matches)) {
            // error_log('prove begins: ' . $statement);
            break;
        }
    }

    // echo 'axiom_prefix: ' . jsonify($axiom_prefix);

    $lengths = [];
    $input = [];
    $inputs = [];
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
                create_html_tag($statement, $axiom_prefix, $input);
            } else if (strpos($theorem, 'Eq.') === false) {

                // error_log('create_a_tag: ' . __LINE__);
                // error_log("statement = $statement");
                $input[] = create_a_tag($theorem, $statement, $axiom_prefix);
            } else {
                create_html_tag($statement, $axiom_prefix, $input);
            }
        } else if (preg_match('/= *apply\(/', $statement, $matches)) {
            create_html_tag($statement, $axiom_prefix, $input);
        } else {
            create_html_tag($statement, $axiom_prefix, $input);
        }

        if (preg_match('/Eq *<< */', $statement, $matches)) {
            if ($input) {
                $inputs = array_merge($inputs, $input);
                unset($input);
            }

            $lengths[] = 1;
        } else if (preg_match('/(Eq\.\w+ *(?:, *(?:Eq\.\w+|\w+|\*\w+) *)*)= */', $statement, $matches)) {
            $statement = $matches[1];
            // error_log("parameter: " . $statement);

            preg_match_all('/Eq\.\w+/', $statement, $matches, PREG_SET_ORDER);

            $lengths[] = count($matches);
            if ($input) {
                $inputs = array_merge($inputs, $input);
                unset($input);
            }
        } else {
            // error_log("python statements: $statement");
        }
    }
    return $inputs;
}

$dirname = dirname(__file__);
$sagemath = basename($dirname);

function to_a_tag($module)
{
    $href = str_replace('.', '/', $module);
    global $sagemath;
    $href = "/$sagemath/$href.php";
    return "<a name=python[] href='$href'>$module</a>";
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

function println(&$dict, $module, $multiplier)
{
    // https://www.php.net/manual/en/function.str-repeat.php
    echo str_repeat("&nbsp;", $multiplier) . to_a_tag($module) . "<br>";
    if (array_key_exists($module, $dict)) {
        foreach ($dict[$module] as $module => $value) {
            println($dict, $module, $multiplier + 8);
        }
    }
}

if (array_key_exists('callee', $_GET)) {    
    echo "the axiom in question is a callee in the following hierarchy:<br>";
    $dict = [];
    foreach (read_all_axioms($dirname . '/axiom') as $py) {
        $caller = to_python_module($py);
        $modules = process_axiom($py);

        foreach ($modules as $callee) {
            if (! array_key_exists($callee, $dict)) {
                $dict[$callee] = [];
            }

            if (! array_key_exists($caller, $dict[$callee])) {
                $dict[$callee][$caller] = 0;
            }
            ++ $dict[$callee][$caller];
        }
    }
    
    $callee = $_GET['callee'];
    println($dict, $callee, 2);    
    echo "<br><br>switch to <a href='request.php?caller=$callee'>caller hierarchy</a>";
} else if (array_key_exists('caller', $_GET)) {
    
    echo "the axiom in question is a caller in the following hierarchy:<br>";
    $dict = [];
    foreach (read_all_axioms($dirname . '/axiom') as $py) {
        $caller = to_python_module($py);
        $modules = process_axiom($py);

        foreach ($modules as $callee) {
            if (! array_key_exists($caller, $dict)) {
                $dict[$caller] = [];
            }

            if (! array_key_exists($callee, $dict[$caller])) {
                $dict[$caller][$callee] = 0;
            }
            ++ $dict[$caller][$callee];
        }
    }
    
    $caller = $_GET['caller'];
    println($dict, $caller, 2);
    echo "<br><br>switch to <a href='request.php?callee=$caller'>callee hierarchy</a>";
}

// exit(0);

?>