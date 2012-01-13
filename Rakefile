require 'bundler'
Bundler.setup

require 'redcarpet'
require 'albino'
require 'nokogiri'

class OpalHTML < Redcarpet::Render::HTML
  def block_code(code, language)
    Albino.new(code, language || :text).colorize
  end
end

desc "index.html"
task "index.html" do
  text = File.read 'index.md'
  markdown = Redcarpet::Markdown.new(OpalHTML, :fenced_code_blocks => true)

  File.open('index.html', 'w+') do |o|
    o.write File.read('pre.html')
    o.write markdown.render(text)
    o.write File.read('post.html')
  end
end
