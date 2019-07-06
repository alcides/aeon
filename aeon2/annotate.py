import subprocess
import os.path
import sys

from .types import *
from .codegen import *


class CostExtractor(object):
    def __init__(self, context, tcontext):
        self.context = context
        self.type_context = tcontext
        self.codegen = CodeGenerator(context, tcontext)

    def default_random(self, type):
        if type == 'Boolean':
            return "return new Random().nextBoolean();"
        if type == 'Integer':
            return "return new Random().nextInt(2000000)-1000000;"
        if type == 'Object':
            return "return new Integer(0);"
        if type == 'java.util.ArrayList<Integer>':
            return """
                    java.util.ArrayList<Integer> lst = new java.util.ArrayList<>();
                    Random r = new Random();
                    for (int i=0;i<r.nextInt(1000000);i++) lst.add(r.nextInt());
                    return lst;
                    """

        if type == "java.util.function.Supplier<Integer>":
            return "return () -> QuickTimeCheck.work(new Random().nextInt());"

        if type == "java.util.function.Consumer<Integer>":
            return "return (Integer a) -> { QuickTimeCheck.work(new Random().nextInt()); };"

        if type == "java.util.function.UnaryOperator<Integer>":
            return "return (Integer n) -> QuickTimeCheck.work(new Random().nextInt());"

        if type == "java.util.function.BiFunction<Integer, Integer, Integer>":
            return "return (Integer a, Integer b) -> QuickTimeCheck.work(new Random().nextInt());"

        print("TODO: No random for ", type)
        return None

    def generate(self, ast):
        name = ast.nodes[0]
        ft = self.context.find(name)
        args_methods = []
        args_invocations = []
        args_invocation_names = []
        while ft.binders:
            ft = ft.copy_replacing_freevar(ft.binders[0], Type('Integer'))

        call = " int counter_i=0; while (counter_i < 100000) {\n"
        for i, arg in enumerate(ft.lambda_parameters):

            self.codegen.push_frame()
            self.codegen.stack[-1]["__argument_{}".format(i)] = arg

            java_type = self.codegen.type_convert(arg)
            generator_name = "generate__random__" + self.javify(str(java_type))
            body = self.default_random(java_type)
            if not body:
                body = "return null;"  # TODO
            meth = """    public static {} {}() {{ {} }}""".format(
                java_type, generator_name, body)
            if generator_name not in args_invocation_names:
                args_methods.append(meth)
                args_invocation_names.append(generator_name)
            args_invocations.append("__argument_{}".format(i))
            call += "{} __argument_{} = {};\n".format(java_type, i,
                                                      generator_name + "()")

        if ft.preconditions:
            ver = "&&".join(
                [str(self.codegen.g_expr(pre)) for pre in ft.preconditions])
            call += "if (!({})) continue;\n".format(ver)

        for i, arg in enumerate(ft.lambda_parameters):
            java_type = self.codegen.type_convert(arg)
            ps = self.type_context.get_type_properties(arg)

            if java_type in ['Integer', 'Double', 'Boolean']:
                call += """System.out.println("__argument_{} = " + __argument_{});\n""".format(
                    i, i)
            elif ps:
                for prop in ps:
                    if len(prop) > 2 and prop[2]:
                        call += """System.out.println("__argument_{}__index__{} = " + {}(__argument_{}));\n""".format(
                            i, prop[0], prop[2], i)
            elif arg.is_function():
                if java_type.startswith("java.util.function.Supplier"):
                    method_name = "get"
                    fargs = ""
                elif java_type.startswith("java.util.function.Consumer"):
                    method_name = "accept"
                    fargs = "null"
                elif java_type.startswith("java.util.function.Function"):
                    method_name = "apply"
                    fargs = "null"
                elif java_type.startswith("java.util.function.BiFunction"):
                    method_name = "apply"
                    fargs = "null, null"
                elif java_type.startswith("java.util.function.UnaryOperator"):
                    method_name = "apply"
                    fargs = "null"
                else:
                    method_name = "get"
                    fargs = ""
                call += """System.out.println("time(__argument_{}) = " + QuickTimeCheck.runAndTime(() -> {{ __argument_{}.{}({}); }}));\n""".format(
                    i, i, method_name, fargs)
            else:
                print("No data for ", arg)
                print("arg:", arg, arg.is_function(), arg.lambda_parameters)

        args = ",".join([str(x) for x in args_invocations])
        call += template_start_timer
        call += "{}({});".format(name, args)
        call += template_end_timer
        call += "\n counter_i++; }"
        methods = "\n".join(args_methods)
        self.codegen.pop_frame()
        return template.format(methods, call)

    def javify(self, name):
        return name.replace(".", "__dot__").replace("<", "__of__").replace(
            ">", "").replace(", ", "__and__").replace(" -> ", "__to__")

    def compile_and_run(self, src):
        classpath = "../bin/AeminiumRuntime.jar"
        with open("bin/QuickTimeCheck.java", "w") as f:
            f.write(src)
        try:
            current_dir = os.path.dirname(os.path.realpath(__file__))
            cmd = "javac -cp {} ../bin/*.java && java -cp {}:../bin QuickTimeCheck".format(
                classpath, classpath)
            output = subprocess.check_output(cmd,
                                             stderr=subprocess.STDOUT,
                                             shell=True,
                                             cwd=current_dir)
            parts = output.decode("utf-8").split("\n")
            parts = list(filter(lambda x: x, parts))

            for p in parts[:-1]:
                print(p)
            return float(parts[-1])
        except subprocess.CalledProcessError as e:
            print("Error:", e.output)
            sys.exit(-1)
            return -1.0
        except ValueError as e:
            raise e

    def root(self, ast):
        for toplevel in ast:
            if toplevel.nodet == 'native':
                if not toplevel.type.effects:
                    klass = self.generate(toplevel)
                    time = self.compile_and_run(klass)
                    print("Time of {} is {}".format(toplevel.nodes[0], time))


def typeinfer(ast, context, tcontext):
    CostExtractor(context, tcontext).root(ast)


template_start_timer = "long init = System.nanoTime();\n"
template_end_timer = "long time = System.nanoTime() - init;\nSystem.out.println(" " + (time / 1000000000.0) );"

template = """
import java.util.Random;

public class QuickTimeCheck {{

{}
    public static int work(int n) {{
        int i = n;
        while (i > 0) i--;
        return i;
    }}
    
    public static double runAndTime(Runnable s) {{
 	   long init = System.nanoTime();
       s.run();
 	   long time = System.nanoTime() - init;
 	   return (time / 1000000000.0);
    }}

    public static void main(String[] args) {{
        {}  
    }}
}}
"""
