puts "In parser"
require 'opal/parser/parser'

puts Opal::Parser
puts Opal::Parser.new
Opal::Parser.new.parse "1"
