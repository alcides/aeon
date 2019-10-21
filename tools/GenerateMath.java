import java.lang.reflect.*;
import java.util.Arrays;

public class GenerateMath {

  public static String box(String b) {
    if (b.equals("int")) return "Integer";
    if (b.equals("float")) return "Float";
    if (b.equals("double")) return "Double";    
    if (b.equals("long")) return "Long";        
    return b;
  }
  
  public static String addName(String b) {
    return "_:" + b;
  }
  
  public static String stringify(Class<?> c) {
    if (c.equals(Integer.class)) return "Integer";
    if (c.equals(Double.class)) return "Double";    
    if (c.equals(Float.class)) return "Float";        
    if (c.equals(Long.class)) return "Long";        
    if (c.equals(Integer.TYPE)) return "Integer";
    if (c.equals(Double.TYPE)) return "Double";    
    if (c.equals(Float.TYPE)) return "Float";        
    if (c.equals(Long.TYPE)) return "Long";        
    return "Object /*unknown*/";
  }

  public static String nativeTo(Class c, Method m) {
    StringBuilder b = new StringBuilder("native ");
    final int modifiers = m.getModifiers();
    
    if (Modifier.isStatic(modifiers)) {
      b.append(c.getName().replace("java.lang.", ""));
      b.append(".");
      b.append(m.getName());
      b.append(" : (");
      Class<?>[] parTypes = m.getParameterTypes();
      if (parTypes.length > 0) {
        String pars = Arrays.stream(parTypes)
          .map(x -> x.toString())
          .map(GenerateMath::box)
          .map(GenerateMath::addName)
          .reduce((x,y) -> x +","+y).get();
        b.append(pars);
      }
      // args
      b.append(") -> ");
      
      b.append(GenerateMath.addName(GenerateMath.box(GenerateMath.stringify(m.getReturnType()))));
    
      return b.toString(); 
    } else {
      return "";
    }
  }

  public static void main(String args[]) {
    try {
      Class c = Math.class;
      Method[] m = c.getDeclaredMethods();
      for (int i = 0; i < m.length; i++)
        System.out.println(nativeTo(c, m[i]));
    } catch (Throwable e) {
      System.err.println(e);
    }
  }
}