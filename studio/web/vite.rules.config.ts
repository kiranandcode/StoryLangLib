import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'

// The Rules view (src/Rules.tsx) as one self-contained script and stylesheet for
// the deslop UI: `npm run build:rules` writes tools/house/deslop_ui/rules-view/,
// which tools/house/deslop_ui/server.py serves at /rules-view/.
export default defineConfig({
  plugins: [react()],
  define: { 'process.env.NODE_ENV': '"production"' },
  build: {
    outDir: '../../tools/house/deslop_ui/rules-view',
    emptyOutDir: true,
    cssCodeSplit: false,
    lib: { entry: 'src/rules-embed.tsx', name: 'RulesEmbed', formats: ['iife'], fileName: () => 'rules-view.js' },
  },
})
