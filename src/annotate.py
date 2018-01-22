import subprocess
import os.path

from .typestructure import *
from .codegen import *

class CostExtractor(object):
    def __init__(self, context, tcontext):
        self.context = context
        self.type_context = tcontext
        self.codegen = CodeGenerator(context, tcontext)
        
    def generate(self, ast):
        name = ast.nodes[0]
        ft = self.context.find(name)
        args_methods = []
        args_invocations = []
        while ft.freevars:
            ft = ft.copy_replacing_freevar(ft.freevars[0], Type('Integer'))
        
        print("Type:", ft)
            
        for arg in ft.arguments:
            java_type = self.codegen.type_convert(arg)
            generator_name = "generate__random__" + self.javify(str(java_type))
            body = "return null;"
            meth = """    public static {} {}() {{ {} }}""".format(java_type, generator_name, body)
            if generator_name + "()" not in args_invocations:
                args_methods.append(meth)
            args_invocations.append(generator_name + "()")

    
        args = ",".join([ str(x) for x in args_invocations ])
        call = "{}({});".format(name, args)
        methods = "\n".join(args_methods)
        return template.format(methods, call)    
        

    def javify(self, name):
        return name.replace(".", "__dot__").replace("<", "__of__").replace(">","").replace(" -> ", "__to__")    
    
    
    def compile_and_run(self, src):
        classpath = "../bin/AeminiumRuntime.jar"
        with open("bin/QuickTimeCheck.java", "w") as f:
            f.write(src)
        try:
            current_dir = os.path.dirname(os.path.realpath(__file__))
            cmd = "javac -cp {} ../bin/*.java && java -cp {}:../bin QuickTimeCheck".format(classpath, classpath)
            output = subprocess.check_output(cmd, stderr=subprocess.STDOUT, shell=True, cwd=current_dir)
            last_part = output.decode("utf-8").split("\n")[-1]
            return float(last_part)
        except subprocess.CalledProcessError as e:
            print("Error:", e.output)
            return -1.0
        
        
    def root(self, ast):
        for toplevel in ast:
            if toplevel.nodet == 'native':
                if not toplevel.type.effects:
                    klass = self.generate(toplevel)
                    time = self.compile_and_run(klass)
                    # TODO
    
def typeinfer(ast, context, tcontext):
    CostExtractor(context, tcontext).root(ast)
            

template = """
public class QuickTimeCheck {{

{}

    public static void main(String[] args) {{
    
        long init = System.nanoTime();
        
        {}
        
        long time = System.nanoTime() - init;
        System.out.print("" + (time / 1000000000.0) );
    }}
}}
"""