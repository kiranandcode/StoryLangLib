import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'

const api = `http://127.0.0.1:${process.env.STUDIO_API_PORT ?? 8765}`

export default defineConfig({
  plugins: [react()],
  server: {
    port: Number(process.env.STUDIO_PORT ?? 5177),
    strictPort: true,
    proxy: { '/api': { target: api, changeOrigin: true } },
  },
})
