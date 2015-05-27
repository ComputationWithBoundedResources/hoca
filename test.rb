#!/usr/bin/ruby

require 'find'

$examples="examples"
$trss="examples/trss"
$hoca="/home/zini/.cabal/bin/pcf2trs +RTS -N -RTS"
$rewrite="/home/zini/bin/rewrite"

$systems = []
Find.find($examples) { |path|
  $systems << path if File.extname(path) == ".fp"
}

$natlist = [
  "Nil" ,
  "Cons(S(0),Nil)",
  "Cons(S(0),Cons(S(S(0)),Nil))",
  "Cons(S(0),Cons(S(S(0)),Nil))",
  "Cons(S(0),Cons(S(S(0)),Cons(S(S(0)),Nil)))",
  "Cons(S(S(0)),Cons(S(S(0)),Cons(S(S(0)),Nil)))",
  "Cons(0,Cons(S(0),Cons(S(S(0)),Nil)))",
  "Cons(S(S(S(0))),Cons(S(0),Cons(S(S(0)),Nil)))"
]

$abclist = [
  "Nil" ,
  "Cons(A,Nil)",
  "Cons(A,Cons(B,Nil))",
  "Cons(A,Cons(C,Nil))",
  "Cons(A,Cons(A,Cons(B,Nil)))",
  "Cons(A,Cons(A,Cons(B,Cons(B,Nil))))",
  "Cons(A,Cons(A,Cons(B,Cons(B,Cons(C,Nil)))))",  
]


$nattree = [
  "Leaf(0)" ,
  "Leaf(S(0))",
  "Node(Leaf(S(0)), Leaf(0))",
  "Node(Leaf(S(0)), Node(Leaf(S(S(0))), Leaf(0)))",
  "Node(Node(Leaf(S(S(0))), Leaf(0)), Leaf(S(0)))",
  "Node(Node(Node(Leaf(S(S(0))), Leaf(0)), Leaf(S(0))), Node(Leaf(S(S(0))), Leaf(0)))",
]

$nat = [
  "0",
  "S(0)", 
  "S(S(0))",
  "S(S(S(0)))",
  "S(S(S(S(S(S(S(S(0))))))))"
]

$binstring = [
  "E",
  "O(E)", 
  "O(O(E))",
  "Z(Z(E))",  
  "O(Z(O(E)))",
  "Z(Z(Z(Z(O(Z(O(Z(O(E)))))))))"
]


$argsFor = {
  "evenodd.fp" => [$nat],
  "fib_llist.fp" => [$nat],
  "fib_memo.fp" => [$nat],
  "flatten.fp" => [$nattree],    
  "foldsum.fp" => [$natlist],
  "flip.fp" => [$binstring],
  "id.fp" => [$nat],
  "isort-fold.fp" => [$natlist],
  "isort.fp" => [$natlist],
  "mappplus.fp" => [$natlist,$nat],
  "mergesort-dc.fp" => [$natlist],
  "okasaki-parser-ab.fp" => [$abclist],
  "okasaki-parser-anbn.fp" => [$abclist],
  "okasaki-parser-string.fp" => [$abclist],          
  "pred.fp" => [$nat],
  "mss.fp" => [$natlist],
  "rev-dl.fp" => [$natlist],
  "rev-fletf.fp" => [$natlist],
  "rev-foldl.fp" => [$natlist],  
  "rev.fp" => [$natlist],
  "rpm-lazy.fp" => [$nattree],      
  "rev.fp"=> [$natlist],
  "sum.fp"=> [$natlist],
  "take_lazy.fp"=> [$nat]  
}

def outFile(inFile)
  "#{$trss}/#{File.basename(inFile,'.*')}.trs"
end

def logFile(inFile)
  "#{$trss}/#{File.basename(inFile,'.*')}.log"
end

def transform(inFile)
  `#{$hoca} +RTS -N3 -RTS #{inFile} > #{outFile(inFile)} 2> #{logFile(inFile)}`
  $?
end 

def cross_product(args)
  if args.empty?
  then [[]]
  else args[0].product(cross_product(args.drop(1))).map! { | as | [as[0]].concat(as[1]) }
  end 
end 

def testArgs(inFile) 
  args = $argsFor[File.basename(inFile)]
  if args.nil?
    []
  else
    cross_product(args)
  end
end


def rewrite(file,args)
  `#{$rewrite} #{file} "main(#{args.join(',')})"`.gsub!(/\s+/,"")
end

def eval_pcf(file,args)
  `#{$hoca} --eval #{file} "#{args.join('" "')}"`.gsub!(/\s+/,"")
end

`echo "" > times`

$systems.each { |s|
  print "transforming #{s}..."
  STDOUT.flush
  t1 = Time.now
  ret = transform(s)
  t2 = Time.now
  `echo '#{s} #{(t2 - t1)}' >> times`
  if ret == 0
  then
    puts "done"
    testArgs(s).each {|c|
      print "  testing #{c.join(',')}..."
      STDOUT.flush
      r = rewrite(outFile(s),c)
      p = eval_pcf(s,c)
      if r == p
      then puts "success"
      else puts "FAILED"
        puts "    pcf result: #{p}"
        puts "    rewrite result: #{r}"
      end
    }
  else puts "FAILED" end
}
